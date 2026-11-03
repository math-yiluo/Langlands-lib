# Finite-type geometry of diagonalizable group schemes

This internal bridge applies the existing affine-spectrum and group-algebra
results to the actual `Diagonalizable.groupScheme R Λ`. Here `R` is any
commutative ring object and `Λ` is any abelian group in the same arbitrary
universe.

`isAffineHom` gives affineness of its structural morphism. The construction is
definitionally the spectrum of the specified algebra map
`R → AddMonoidAlgebra R Λ`, so this follows from affineness of spectrum maps.

`locallyOfFiniteType` additionally assumes `AddGroup.FG Λ`. Mathlib converts
finite generation as a group to finite generation as an additive monoid and
proves that the monoid algebra is a finitely generated algebra. The
`HasRingHomProperty.Spec_iff` characterization of local finite type transfers
that result to the structural morphism. Affineness also supplies
quasi-compactness through the existing instances.

The complete character group is retained, with no torsion-free or
characteristic assumption. These lemmas assert no smoothness. They supply
the acting-group geometry needed when applying an affine finite-type
cocycle-model construction to a diagonalizable action.
