/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once


#include <vector>
#include "traits.hpp"
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include <fstream>
#include "operations.hpp"
#include "static_truth_table.hpp"
#include "dynamic_truth_table.hpp"
#include "bit_operations.hpp"

enum Constraint_Type {
  G , L, E
};

struct Constraint {
  std::vector<uint64_t> variables;
  std::vector<int64_t> coefficients;
  Constraint_Type type;
  int constant;
};

namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt_fstar The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold(TT& tt, std::vector<int64_t>* plf = nullptr )
{
  bool negative_unate;
  bool positive_unate;
  std::vector<Constraint> constraints;
  std::vector<int64_t> linear_form;

  for ( uint64_t var_i = 0u; var_i < tt.num_vars(); var_i++ )
  { /*scroll every variable*/

    auto const tt_cof0 = cofactor0( tt, var_i ); /*for every var writes cofactor0*/
    auto const tt_cof1 = cofactor1( tt, var_i ); /*for every var writes cofactor1*/

    negative_unate = implies (tt_cof1,tt_cof0);
    positive_unate = implies (tt_cof0,tt_cof1);

    if(negative_unate)
    {
      flip_inplace( tt, var_i );
    }

    if(!negative_unate && !positive_unate)
    {
      return false;
    }
  }

  /*variables*/
  for(uint64_t bit_i =0; bit_i < tt.num_bits(); bit_i++){ /*create constraints for every row*/
    Constraint constr;
    for(uint64_t var_i = 0; var_i < tt.num_vars(); var_i++)
    {
      constr.variables.emplace_back( var_i );
    }

      if( get_bit( tt, bit_i ) == 1){
        constr.type = G;
        constr.constant = 0;
      }
      else if(get_bit(tt, bit_i ) == 0){
        constr.type = L;
        constr.constant = -1;
      }
      constr.variables.emplace_back(tt.num_vars()); /*add T*/
    constraints.emplace_back( constr );
  }

  /*filling table with 0 and 1*/
  for(uint64_t var_i = 0; var_i < tt.num_vars(); var_i++){

    uint64_t cycle_length = 1u << var_i;
    uint8_t coef =0;
    uint64_t bit_i = 0;

    while ( bit_i < tt.num_bits() )
    {
      for (uint32_t j = 0; j < cycle_length; j++ ){
        constraints[bit_i].coefficients.emplace_back( coef );
        bit_i++;
      }
      coef= !coef;
    }
  }

  /*coef T*/
  for(uint64_t bit_i = 0; bit_i < tt.num_bits(); bit_i++){
    constraints[bit_i].coefficients.emplace_back(-1);
  }

  /*weights must be positive*/
  for(uint64_t var_i = 0; var_i <= tt.num_vars(); var_i++){
    Constraint constraint;
  for(uint64_t i = 0; i <= tt.num_vars(); i++){ /*coeff of other variables are 0*/
     constraint.coefficients.emplace_back(0);
  }
    constraint.variables.emplace_back( var_i );
    constraint.coefficients[var_i] = 1; /*coef = 1 only for the variable that i consider*/
    constraint.constant = 0;
    constraint.type = G;
    constraints.emplace_back(constraint);
  }


  lprec *lp;
  auto n_rows = constraints.size();
  std::vector<double> row;

  lp = make_lp(0, tt.num_vars()+1);
  if(lp == nullptr) {
    fprintf(stderr, "Unable to create new LP model\n");
    return(false);
  }

  set_add_rowmode(lp, TRUE);

  row.emplace_back(1.0);
  for(uint64_t col = 1; col<=tt.num_vars()+1; col++){
    row.emplace_back(1.0);
  }

  set_obj_fn(lp, row.data());

  for(uint64_t rows = 0; rows < n_rows; rows++){
    for(uint64_t col = 1; col <= tt.num_vars()+1; col++){
      row[col] = constraints[rows].coefficients[col-1];
    }
    if(constraints[rows].type == G )
      add_constraint(lp, row.data(), GE, constraints[rows].constant);
    else if (constraints[rows].type == L)
      add_constraint(lp, row.data(), LE, constraints[rows].constant);
  }

  set_add_rowmode(lp, FALSE);
  set_minim(lp);
  print_lp(lp);
  set_verbose(lp, IMPORTANT);

  for(auto i = 1u; i< tt.num_vars()+1; i++){
    set_int(lp, i, TRUE);
  }

  int ret = solve(lp);
  if(ret == OPTIMAL){
    printf("Objective value: %f\n", get_objective(lp));

    get_variables(lp, row.data());
    for(uint64_t i = 0; i < tt.num_vars()+1; i++){
      linear_form.push_back((int)(row[i]));
    }

    for(uint64_t j = 0; j <= tt.num_vars() +1; j++){
      printf( "%s: %f\n", get_col_name( lp, j + 1 ), row[j] );
    }
  }
  else
    return false;

  if ( plf ){
    *plf = linear_form;
  }
  return true;
}


} /* namespace kitty */
