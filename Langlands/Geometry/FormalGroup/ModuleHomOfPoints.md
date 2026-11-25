# Formal module homomorphisms from actual point maps

This internal construction upgrades the
nilpotent-point reconstruction to formal O-module homomorphisms. O is
a commutative ring, R is a commutative O-algebra, their universes may
differ, and both coordinate types are finite. Test R-algebras have the
universe of R.

`Hom.ext_onAlgebraPoints` proves that two actual formal O-module
homomorphisms are equal if their evaluations agree on every actual
nilpotent point over every test algebra. It uses coefficient
reconstruction for pointed coordinate maps.

`Hom.ofNatural` takes a family of maps on those actual points that is
natural in the coefficient algebra, additive, and O-linear. Additivity
first implies preservation of zero. The coordinate reconstruction
therefore gives a pointed formal map. Evaluate the formal addition
equation on all nilpotent tuples, split paired tuples into their two
components, and use additivity of the family. Coordinate extensionality
then proves the actual formal group homomorphism equation. The same
argument with each scalar action proves formal O-linearity.

`onAlgebraPoints_ofNatural` identifies evaluation of the constructed
formal homomorphism with the original pointwise family. This is an
actual reconstruction theorem; no formal homomorphism is assumed as
part of the input family. Its provenance is internal infrastructure
for `LocalQuasiIsogenyInverseStatement`, not an external source
quotation.
