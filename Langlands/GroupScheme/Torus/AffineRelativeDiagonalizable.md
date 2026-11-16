# Affine and relative diagonalizable models

This internal comparison connects two published models of the same
diagonalizable group over an affine base.

For an arbitrary commutative ring `R` and an additive commutative group
`M` in the same universe, `Diagonalizable.relativeModelIso R M` is an
actual group-scheme isomorphism from the affine group-algebra model
`(Diagonalizable.groupScheme R M).toGrp` to
`RelativeMultiplicativeType.diagonalizable (Spec R) M`.
The latter is defined by pulling the integral diagonalizable model back
along the unique morphism `Spec R → Spec (ULift ℤ)`.

The implementation takes the inverse of the published
`Diagonalizable.baseChangeIso` for precisely that morphism. Hence it is
valid on every test scheme, for arbitrary rings and arbitrary abelian
character groups, with no reducedness, smoothness or torsion-freeness
assumption.

`Diagonalizable.isDiagonalizable_groupScheme` uses this isomorphism to
prove the published relative `IsDiagonalizable` predicate when `M` is
finitely generated. This finite-generation assumption is exactly the
one in that predicate. In particular it permits torsion character groups
such as the unsaturated root-lattice quotients used to construct
scheme-theoretic centres.

Provenance: this is a derived internal identification of existing
Library definitions, proved solely by the existing arbitrary-base-change
comparison for diagonalizable group schemes.
