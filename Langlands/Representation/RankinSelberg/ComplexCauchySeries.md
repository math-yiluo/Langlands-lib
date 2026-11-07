# Complex specialization of the Cauchy series

Author: Worker 1767.

This internal helper evaluates the two polynomial alphabets at arbitrary
supplied complex tuples, permitting repeated and zero entries. Coefficient-ring
transport preserves the complete symmetric and Jacobi–Trudi polynomials, so
the specialized degree coefficient is the finite sum of the actual evaluated
Jacobi–Trudi factors over partitions of that degree.

Mapping the formal inverse identity gives the product of the linear pair
factors as the inverse denominator of the specialized formal series.
Alternatively, the complete generating-series product and formal rescaling
identify the specialized series with the finite product of the geometric
series for all parameter products `x i * y j`. These are formal equalities;
no series is analytically evaluated and no convergence is asserted here.
