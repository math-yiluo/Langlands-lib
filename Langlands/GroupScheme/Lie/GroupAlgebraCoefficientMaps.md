# Coefficient maps for actual Lie kernels

Let `G` be an affine group scheme over a commutative ring `R`, let `A` be any
commutative `R`-algebra in the same universe, and let `M` be an additive
commutative monoid. `kernelCoefficient G A M m` reads the coefficient indexed
by `m` of an actual Lie vector over `AddMonoidAlgebra A M` and returns an
actual Lie vector over `A`. The map is `A`-linear, with the source module
obtained by restricting the existing group-algebra module to `A`.

This is internal infrastructure for the weight-decomposition proof. The
motivating source is Milne, *Algebraic Groups* (2017), 12.12, printed
pp.234–235 (PDF250–251), whose proof extracts character eigenvectors from
coefficients in a group-like basis. The arbitrary-base coefficient maps
and their compatibility lemmas here are derived from the actual-kernel
coordinate comparison; Milne is cited as motivation for the method. This
file does not assert weight decomposition.

The coordinate algebra acts through the identity augmentation.
`originCoefficientMap` is linear for this action because multiplication by
a constant monomial multiplies each coefficient by the same scalar.
Postcomposing identity derivations with that map, and transporting back
through `kernelDerivationLinearEquiv`, defines `kernelCoefficient`.
The coefficient formula fixes its meaning. It also shows that all the
coefficients together distinguish Lie vectors.

The naturality formula for the kernel-to-derivation comparison implies
`kernelCoefficient_map`: coefficient extraction commutes with an algebra
homomorphism applied to the coefficient ring. A monomial times the
constant extension of a vector has that vector's scalar multiple as its
single nonzero coefficient, as expressed by `kernelCoefficient_monomial`.
These results require affineness but no finite-type hypothesis.

When `G` is also locally of finite type, its coordinate algebra is finitely
generated over `R`. The union of the supports of a derivation on a finite
set of algebra generators bounds all its nonzero coefficient derivations:
a derivation vanishing on those generators is zero. This proves
`kernelCoefficient_finite`. `kernelCoefficients` packages the individual
coefficients as a finite, `A`-linear family. It extends the base-ring
coefficient construction of `GroupAlgebraCoordinates` to arbitrary
coefficient algebras and supplies explicit monomial reconstruction.
`kernelCoefficients_reconstruct` follows by reading every coefficient of
the finite sum and using `kernelCoefficient_ext`.

Finally, `kernelCoefficient_adjoint` states that constant adjoint actions
commute with coefficient extraction. Its proof reconstructs the vector
as a finite sum of monomial multiples of constant vectors. Linearity of
the actual adjoint action and its test-algebra naturality compute the
action on each summand. Reading a coefficient then gives the asserted
adjoint action over `A`. This lemma uses local finite type to justify
that finite reconstruction; no smoothness or field hypothesis is needed.
