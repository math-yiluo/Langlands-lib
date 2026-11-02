# Group-algebra coefficients of actual Lie kernels

Let `G` be an affine group scheme locally of finite type over a commutative
ring `R`, and let `M` be any additive commutative monoid. The construction
`kernelGroupAlgebraCoefficients` is an `R`-linear equivalence

`Additive (lieKernel G (AddMonoidAlgebra R M)) ≃ₗ[R] (M →₀ Additive (lieKernel G R))`.

The source carries the existing test-algebra module structure restricted to
`R`. No field, smoothness, flatness, or finiteness assumption on `M` is used.
The coefficient Lie vectors are elements of the original dual-number identity
kernel, with its existing operations.

This is an internal prerequisite for the universal-point proof of weight
decomposition. The motivating source is Milne, *Algebraic Groups* (2017),
12.12, printed pp.234–235 (PDF250–251). The source proves character-space
decomposition for diagonalizable representations over a field. This file's
arbitrary-base group-algebra coefficient equivalence is derived directly from
the affine-coordinate comparison and finite algebra generation; it is not
claimed as a theorem stated by Milne. It does not yet construct the weight
decomposition.

`coordinateAlgebraFiniteType` transports local finite type along the chosen
affine presentation `coordinateIso`. The relative spectrum criterion for
finite type then shows that `coordinateAlgebra G` is a finite-type
`R`-algebra.

The coordinate algebra acts on each test algebra through the identity
augmentation. For the group algebra, multiplication by the augmentation's
constant monomial has coefficients equal to the augmentation scalar times
the original coefficients. This proves the coordinate-algebra linearity of
`originCoefficientLinearEquiv`, which reads the finitely supported coefficient
function of a group-algebra element.

The final equivalence first applies `kernelDerivationLinearEquiv`, then
postcomposes derivations with the coefficient equivalence, then uses
`derivationFinsuppLinearEquiv`, and finally converts each coefficient
derivation back to an actual base-ring Lie vector. Finite algebra generation
in the derivation equivalence gives a uniform finite support for this family.
Its inverse assembles the coefficient derivations and uses the same
comparisons in reverse. Additivity follows from those comparisons; base-ring
linearity follows by expressing a restricted scalar as a constant monomial
and reading its product's coefficients.

`kernelGroupAlgebraCoefficients_apply` specifies the coefficients: evaluating
the identity derivation of coefficient `m` at a coordinate `c` gives exactly
coefficient `m` of the original group-algebra-valued derivation at `c`.
