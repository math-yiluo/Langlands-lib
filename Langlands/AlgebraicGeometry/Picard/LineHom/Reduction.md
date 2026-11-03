# Arbitrary-base reduction for proper line-bundle Hom

This internal module proves that `LineHom.NoetherianModelStatement.{u}`
implies the exact `Picard.ProperLineBundleHomRepresentabilityStatement.{u}`.
The noetherian model statement remains an explicit hypothesis. This module
does not prove that statement or unconditional Hom representability.

The reduction first starts from proper flat geometry over a noetherian ring
`C`, whose base change to a ring `A` is the given scheme. It descends the
first line bundle to a finitely generated `C`-subalgebra `B` of `A`, using
`NoetherianApproximation.lineBundleSubalgebraDescent`. The comparison to the
chosen base change over `B` is Cartesian by the published intermediate-stage
comparison lemma. It then descends the second line bundle to a finitely
generated `B`-subalgebra `D` of `A`. Pulling the first descended bundle back
to `D` gives two actual rank-one modules on the same proper flat scheme.
Both `B` and `D` are noetherian by finite type over a noetherian ring.
Pullback composition and its congruence isomorphism identify these two
modules' pullbacks with the original modules.

Apply the assumed noetherian finite linear model theorem at `D`. Its
`HasModel.exists_representation` result gives an actual affine locally
finitely presented representing scheme. Restrict this representation along
`Spec A → Spec D`, and transport it along
`CoherentSheaves.intrinsicModuleHomCartesianOfIso`. This is a natural
isomorphism of the full presheaves, including all ordinary module maps and
all restriction maps, rather than a bijection only on affine tests.

For arbitrary affine base `Spec R`, take the prime subring
`(⊥ : Subalgebra ℤ R)`, which lies in the original universe and is noetherian.
The published theorem
`AlgebraicGeometry.exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation`
descends the proper flat finitely presented geometry to a finitely generated
subalgebra of `R` over that prime subring. The preceding two-bundle argument
then gives the desired representation over `Spec R`.

For an arbitrary base scheme, apply the affine result after each chart of
its affine open cover. The published intrinsic-Hom base-change isomorphism
identifies these representations with restrictions of the given Hom
presheaf. A line bundle is quasi-coherent, so actual Hom is an fppf sheaf.
`AlgebraicSpace.LocalRepresentation.exists_affine_representation` glues the
representatives and retains affineness and local finite presentation of
the structure morphism. Applying this result to the actual relative
projection over an arbitrary parameter scheme proves the conditional
focused proposition.

The argument uses only published geometric approximation, line-bundle
descent, ordinary module pullback and full-slice gluing. Its provenance is
internal composition of these results; no new source theorem is assumed.
All schemes and rings retain universe `u`. The base, parameter scheme and
test schemes are arbitrary, including empty, nonreduced, nonnoetherian and
non-quasi-compact schemes, and the proper schemes need not be projective.
