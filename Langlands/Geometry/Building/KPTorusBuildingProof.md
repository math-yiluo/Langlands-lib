# Tori and KP building data: proof of `KPTorusBuildingStatement`

The theorem `Langlands.Geometry.Building.kpTorusBuilding` proves exactly
`Langlands.Geometry.Building.KPTorusBuildingStatement.{u}` of
`Langlands.Geometry.Building.KPTorusRegressionStatement`, at an arbitrary universe `u`. The
statement's Markdown records the sources (Kaletha–Prasad, *Bruhat–Tits theory: a new approach*,
2023, and the corrections of 1 November 2024) and the meaning of every object. The proof adds no
premise: for every torus `T` over a nonarchimedean local field `F` and every
`D : KPBuildingDatum T` with `D.SatisfiesGroupAxioms`, all conclusions are derived from the
torus hypothesis and from the Axiom 4.1.20 clause `neutral_points` of `D`. No other clause of
`D.SatisfiesGroupAxioms` is used.

The module also proves helper results, stated for any supplied `B : ValuationBuildingData T`,
`P : ParahoricBuildingData T` or `D : KPBuildingDatum T` with `IsTorus T`; they are listed below.

## Commutativity

A torus is commutative: `IsTorus.isCommMonObj`. The Library's
`RelativeTorus.IsTorus.commGroupScheme` applied to `hT.isRelativeTorus` is the same group scheme
`T` with its commutative law, and its underlying group scheme is `T` by definition. The proofs
use it to apply the Library's results on commutative ambient groups to the supplied data of `T`.

## The reduced building, facets and stabilizers

- `ValuationBuildingData.subsingleton_reducedBuilding_of_isTorus`: the reduced building has at
  most one point. This is the Library's
  `ValuationBuildingData.subsingleton_reducedBuilding_of_commutative`: a split subtorus of a
  commutative group has no relative roots, so the apartment is one point, and every rational
  point normalizes the maximal split torus, so every point of the quotient (7.6.2) equals the
  image of that point.
- `ValuationBuildingData.nonempty_unique_reducedBuilding_of_isTorus`: exactly one point, since
  the apartment is nonempty (an affine space) and maps to the building.
- `ValuationBuildingData.relativeRoots_eq_empty_of_isTorus`: no relative roots, by the Library's
  `ValuationBuildingData.relativeRoots_eq_empty_of_commutative`.
- `ValuationBuildingData.nonempty_unique_buildingFacet_of_isTorus`: exactly one facet. Without
  relative roots the facets of the building are exactly the singleton subsets
  (`ValuationBuildingData.isFacet_iff_exists_singleton_of_relativeRoots_eq_empty`), and there is
  one point.
- `ValuationBuildingData.fixer_eq_top_of_isTorus` and
  `ValuationBuildingData.pointwiseFixer_eq_top_of_isTorus`: every element of `T(F)` fixes every
  point, because there is only one.
- `ValuationBuildingData.compactStabilizer_eq_of_isTorus`: `B.compactStabilizer y = T(F)^1`, by
  the definition `T(F)^1 ⊓ B.fixer y` and the previous item.
- `ValuationBuildingData.enlargedStabilizer_eq_of_isTorus`: every point of the enlarged building
  has stabilizer `T(F)^1`, by the Library's
  `ValuationBuildingData.enlargedStabilizer_eq_compactStabilizer` and the previous item.

## The zero subgroup and the parahoric

- `simplyConnectedImage_eq_bot_of_isCommMonObj`: for a separated commutative group scheme `G`
  and maps `π : C → D`, `d : D → G` with `IsSimplyConnectedDerivedCover d π`, the image of
  `C(F) → G(F)` is trivial. The image lies in the derived subgroup
  (`IsSimplyConnectedDerivedCover.range_comp_le_derivedSubgroup`), which is trivial for a
  commutative group (`derivedSubgroup_eq_bot_of_isCommMonObj`).
- `ParahoricBuildingData.zeroSubgroup_eq_of_isTorus`: for a torus,
  `G(F)^0 = G(F)^♮ ⊔ Z(F)^0` (KP Definition 2.6.23(3)) is the image of `Z(F)^0` in `T(F)`,
  since `G(F)^♮` is trivial by the previous item.
- `KPBuildingDatum.parahoric_eq_of_isTorus`: if `D.SatisfiesGroupAxioms`, then
  `D.parahoric x` is the image of `D.base.centralizerZero` for every facet `x`. The parahoric is
  the integral-point group of the neutral model of the facet, and Axiom 4.1.20
  (`BuildingModelFamily.ModelAxiomClauses.neutral_points`, the field
  `hD.bruhatTitsGroupSchemes.neutral_points`) identifies it with the pointwise fixer of the
  facet intersected with `G(F)^0`. The pointwise fixer is all of `T(F)`, and `G(F)^0` is the
  image of `Z(F)^0` by the previous item.

The inclusion `T(F)^0 ≤ T(F)^1` is the Library's
`ZeroSubgroupDatum.map_centralizerZero_le_zeroSubgroup` followed by
`ZeroSubgroupDatum.zeroSubgroup_le_rationalCommonNormKernel` (KP Lemma 2.5.14).

## The central factor and the enlarged building

`centralFactor_finiteDimensional_finrank` proves that `CentralFactor T` is finite-dimensional
and that `finrank ℝ (CentralFactor T) = splitRank T` in `ℕ∞`. It uses no building data. The
commutative group `T` has a largest split subtorus `i : A → T` (`exists_largestSplitSubtorus`),
which is a maximal split torus (`IsLargestSplitSubtorus.isMaximalSplitTorus`) and a split
component of `T`. Restriction of rational characters along `i` is injective
(`IsLargestSplitSubtorus.characterRestrict_injective`) with finite-index range
(`IsSplitComponent.finiteIndex_range_characterRestrict`). The Library's real comparison
`BruhatTits.Cartan.restrictionEvaluationEquiv` is then a real-linear isomorphism from the real
cocharacter space `V(A)` to `Hom(X^*_F(T), ℝ)`, which is `CentralFactor T` through
`CentralFactor.dualEquiv`. The space `V(A)` is finite-dimensional of dimension the rank of `A`
(`IsSplitTorus.finite_realCocharacterSpace`, `IsSplitTorus.finrank_realCocharacterSpace`), and
that rank is the split rank of `T` by the published conjugacy theorem
`maximalSplitTorusConjugacy` through `splitRank_eq_splitTorusRank_of_conjugacyStatement`.

`ValuationBuildingData.nonempty_unique_enlargedBuilding_iff_of_isTorus`: since the reduced
building is one point, the enlarged building `B.ReducedBuilding × CentralFactor T` is one point
exactly when `CentralFactor T` is, that is (`Module.finrank_zero_iff`) when its dimension is
zero, that is when `splitRank T = 0`, which is `IsAnisotropic T`.

## The theorem

`kpTorusBuilding` installs `IsAffineHom T.X.hom` from `hT.isRelativeTorus.isAffineHom`, as the
statement does, and assembles the items above in the order of the statement: the dimension of
`CentralFactor T`; for each `D` with `D.SatisfiesGroupAxioms`, the unique point of the reduced
building, the criterion for the enlarged building, the unique facet, `T(F)^0 ≤ T(F)^1`, the
parahoric, the compact and full stabilizers of every point, and the stabilizers of the points
of the enlarged building.

## Provenance

This is an internal composition of the Library results named above. It follows the arguments
recorded in the statement's Markdown: no relative roots for a torus, the stabilizers of
KP Lemmas 4.3.1 and 4.3.3, KP Lemma 2.5.14, and Axiom 4.1.20 with the trivial image of the simply
connected cover for the parahoric. The dimension of the central factor is obtained through the
real comparison of a maximal split torus with the rational characters, rather than quoted.
