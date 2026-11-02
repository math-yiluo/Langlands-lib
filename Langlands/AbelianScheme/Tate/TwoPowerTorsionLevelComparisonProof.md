# Comparing the actual two-power torsion levels

`Langlands.AbelianScheme.Tate.twoPowerTorsionLevelComparison` proves
`TwoPowerTorsionLevelComparisonStatement.{u}` for actual abelian schemes
over an arbitrary field. It uses the existing `levelMap` on actual sections.

The underlying closed immersion is a monomorphism of schemes and hence
also a monomorphism in the category over the field. Equality after applying
the level map therefore implies equality of the underlying sections and
then of the elements of the existing torsion level. This proves injectivity.

For surjectivity, take an actual ambient section `s` killed by `2 ^ n`.
The image of the unique point of `Spec K` belongs to the two-power torsion
locus, so it lies in the image of the closed immersion. Since the spectrum
of a field has only one point, the whole range of `s` lies in that image.

The imported `exists_factor_closedImmersion_of_reduced` lemma base changes the closed immersion along
`s`. Its second projection is a surjective closed immersion into the
reduced source `Spec K`, so Mathlib's reduced-target criterion makes that
projection an isomorphism. Its inverse followed by the first projection
gives the lifted section. Compatibility with the structure maps makes this
a section over the field. Postcomposition with the closed immersion
preserves powers and the identity. Monomorphism cancellation now proves
that the lift is killed by the same `2 ^ n`, giving a preimage in the
actual torsion level.

This is an internal derivation from the existing section group operations,
scheme pullbacks, and Mathlib's reduced-target closed-immersion theorem.
The factorization lemma is reused from the published
`TwoPowerTorsionClosureGroupGeometry` module, alongside the unchanged
level-comparison statement. No existence of a closed realization, numerical
torsion formula, dimension equality, or density result is proved here.
