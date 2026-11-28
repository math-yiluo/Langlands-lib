# Anisotropic tori and KP building data: proof of `KPAnisotropicTorusStatement`

The theorem `Langlands.Geometry.Building.kpAnisotropicTorus` proves exactly
`Langlands.Geometry.Building.KPAnisotropicTorusStatement.{u}` of
`Langlands.Geometry.Building.KPTorusRegressionStatement`, at an arbitrary universe `u`. The
statement's Markdown records the sources (Kaletha–Prasad, *Bruhat–Tits theory: a new approach*,
2023, and the corrections of 1 November 2024) and the meaning of every object. The proof adds no
premise.

Let `T` be a torus over a nonarchimedean local field `F` with `IsAnisotropic T` (split rank
zero). The proof installs `IsAffineHom T.X.hom` from `hT.isRelativeTorus.isAffineHom`, as the
statement does, and obtains `IsConnectedReductive T` from
`IsTorus.isConnectedReductive_of_fieldSplitting`.

1. `T(F)^1 = T(F)`. This is the Library's `IsAnisotropic.rationalCommonNormKernel_eq_top`, which
   holds for every anisotropic connected reductive group: it has no nontrivial rational
   character.
2. `T(F)` is compact in `rationalPointTopology F T.X`. This is the implication from anisotropy to
   compactness in the Library's `anisotropicCompactness_proof`, which proves
   `AnisotropicCompactnessStatement`: for a connected reductive group the full set of rational
   points is compact in the canonical topology exactly when the group is anisotropic. The
   instances `IsAffineHom T.X.hom` and `IsAffine T.X.left` used there are propositions, so they
   agree with those of the statement, and the topology is the same.
3. For every `D : KPBuildingDatum T` with `D.SatisfiesGroupAxioms` and every point `z` of the
   enlarged building, the stabilizer of `z` is all of `T(F)`. The stabilizer of `z` equals the
   compact stabilizer of its image in the reduced building
   (`ValuationBuildingData.enlargedStabilizer_eq_compactStabilizer`). The torus `T` with its
   commutative law is `RelativeTorus.IsTorus.commGroupScheme` applied to
   `hT.isRelativeTorus`, whose underlying group scheme is `T` by definition; the Library's
   `ValuationBuildingData.compactStabilizer_eq_normKernel_of_commutative` then identifies that
   compact stabilizer with `T(F)^1`, which is `T(F)` by item 1. The axioms of `D` are not used.

## Provenance

This is an internal composition of the Library results named above. It follows the arguments
recorded in the statement's Markdown: an anisotropic torus has no nontrivial rational
characters, its rational points are compact (the local-field consequence of KP Theorem 2.2.9 in
`anisotropicCompactness_proof`), and the stabilizers of the enlarged building are `T(F)^1`
(KP Lemmas 4.3.1 and 4.3.3).
