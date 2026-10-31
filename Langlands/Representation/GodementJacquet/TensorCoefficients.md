# Products of actual external-tensor coefficients

This derived module concerns finite external tensor products of admissible
complex representations of topological groups with cofinal compact open
subgroups. The index, group and coefficient-carrier universes are independent.

`productCoefficientGenerators` consists of pointwise products of actual factor
matrix coefficients, each formed from a smooth functional and a vector of its
factor representation. Admissibility makes every factor vector smooth.

`matrixCoefficient_external_mem_product_span` proves that every coefficient of
the external tensor product with a smooth functional belongs to the complex
span of these products. The published surjectivity of `smoothDualTensorMap`
expresses that functional as an actual finite tensor of smooth functionals.
Tensor induction in the functional and the vector reduces the coefficient to
the published pure-tensor coefficient formula. Linearity handles scalar
multiples and sums.

`biSmoothMatrixCoefficients_external` proves equality for the entire actual
bi-smooth coefficient space. The forward inclusion uses the preceding
expansion on every generating coefficient. The reverse inclusion constructs
the pure tensor functional and vector; smoothness follows from the smoothness
of the factors and the canonical smooth-dual tensor map.

`exists_finite_productCoefficient_expansion` exposes the equality as an actual
finite sum, choosing a finite set of generating functions, scalar coefficients,
and the smooth factor functionals and vectors producing each term. Its
coefficients and factors are chosen before the group variable.

This is an internal consequence of the published tensor, smooth-dual and
matrix-coefficient APIs. It establishes an actual coefficient expansion. It
asserts no expansion, convergence, rational continuation or reverse generation
of noncompact matrix zeta integrals.
