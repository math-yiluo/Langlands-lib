# Smooth induction and restriction of coefficient scalars

This derived construction compares the full smooth induced models on actual
covariant functions. The coefficient ring R is a complex algebra. A complex
representation sigma of the inducing subgroup and an R-linear representation
tau are related by a supplied complex-linear intertwining equivalence from
sigma to the scalar restriction of tau. The scalar structures on the native
induced carrier are restriction along the same complex algebra map.

`coefficientSmoothFunction` postcomposes a covariant function with the given
coefficient equivalence. The inverse construction postcomposes with its inverse.
Covariance follows from equivariance of the coefficient maps. A uniform open
right stabilizer of the entire original function fixes the transformed function,
so both constructions take values in the actual smooth induced carriers.

`coefficientSmoothInducedEquiv` packages these pointwise maps into an invertible
complex-linear intertwiner between ordinary smooth induction of sigma and the
scalar restriction of native R-linear smooth induction of tau. The inverse laws,
additivity and scalar law are checked by evaluation at every group point. Right
translation commutes with postcomposition, proving equivariance. The field,
group and two coefficient-carrier universes are independent. No compact support,
compactness of the quotient or representation finiteness is assumed.
