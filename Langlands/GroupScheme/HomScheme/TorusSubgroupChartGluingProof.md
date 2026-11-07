# Gluing open charts into the smooth moduli of closed torus subgroups

Author: Worker 1535. The supporting construction modules imported here are
by Worker 1726 (`AdmissibleChartGluing`, `AdmissibleClosedRepresentability`,
`AdmissibleDescent`, `AdmissibleSheaf` and their dependencies) and by
Worker 1535 (`Langlands.AlgebraicGeometry.ClosedSubschemeGluing`).

This module proves the Library statement
`Langlands.GroupScheme.TorusSubgroupModuli.ChartGluingStatement.{u}` as the
theorem `Langlands.GroupScheme.TorusSubgroupModuli.chartGluing`, uniformly in
the universe `u`. The statement says the following. Suppose every smooth
affine group scheme over every `S : Scheme.{u}` has a chart cover: a family
of closed torus families `j k : K k ⟶ G_{U k}` over `U k : Over S`, indexed
by `ι : Type u`, with each `j k` an `IsOpenChart` and the family
`CoversFieldPoints`. Then every such `G` has a smooth `M → S`, a relative
torus `K` over `M` and a closed subgroup inclusion `j : K ⟶ G_M` satisfying
the all-test universality condition `IsUniversal`.

The proof has three steps.

## 1. Closed scheme representatives of locally admissible subgroups

`SubgroupFunctor.exists_isSchemeRepresentedBy` applies to a subgroup functor
`F` of a group scheme `G` over `S`. It assumes that `F` has Zariski-local
membership (`IsZariskiLocal F`), and that `F.baseChange (𝒰.f i)` is
admissible for every member of an open cover `𝒰` of `S`. It concludes that
there is a closed immersion `j : Z ⟶ G.X.left` with
`F.IsSchemeRepresentedBy j`. That is, a scheme map `x : Y ⟶ G.X.left`
satisfies the absolute membership condition `F.schemeCondition x` exactly
when `x` factors through `j`.

The proof applies the generic gluing theorem
`Scheme.ClosedSubschemeGluing.exists_isClosedImmersion` to the condition
`P x := F.schemeCondition x` on maps into `X := G.X.left`:

* `P` is stable under precomposition by `schemeCondition_comp`.
* The open cover of `X` is the pullback `𝒰.pullback₁ G.X.hom` of the base
  cover to the ambient scheme, with its open immersions and covering
  property.
* On each member, the local closed subscheme and the chart condition
  `IsChart` come from `exists_localClosedSubscheme`. This takes the
  underlying inclusion of a chosen admissible representative of each base
  change.
* `P` is local on the source. Given opens `U p` around each point `p` of a
  test scheme `Z` on which the condition holds, form the open cover of `Z`
  by these opens (`Scheme.Cover.mkOfCovers`). Then apply
  `schemeCondition_iff_openCover`, which uses `IsZariskiLocal F`.

The glued closed immersion is the required `j`.

## 2. Effective descent of admissible families

`hasEffectiveAdmissibleDescent G` proves the effective-descent hypothesis
`HasEffectiveAdmissibleDescent G` for every group scheme `G` over every
base `S`. The hypothesis takes a test `T : Over S`, an open cover `𝒰` of
`T.left` and a matching family `F` of admissible subgroups over the cover.
It concludes that the descended subgroup `matchingSubgroup 𝒰 F` is
admissible.

* By `baseChange_matchingSubgroup`, the base change of `matchingSubgroup 𝒰 F`
  to each `𝒰.f i` is the admissible subgroup `coverSubgroup 𝒰 F i`.
* By `isZariskiLocal_matchingSubgroup`, `matchingSubgroup 𝒰 F` has
  Zariski-local membership.
* Step 1 therefore gives a closed scheme representative.
  `isClosedRepresentable_of_schemeCondition` turns it into an actual closed
  subgroup inclusion representing `matchingSubgroup 𝒰 F`, with its group
  structure.
* `isAdmissible_matchingSubgroup_of_isClosedRepresentable` concludes that
  `matchingSubgroup 𝒰 F` is admissible. This step proves the torus property
  locally on the cover.

## 3. Gluing the charts

`chartGluing` assumes `ChartCoverStatement.{u}`. Given `S`, `G` and the
instances `Smooth G.X.hom` and `IsAffineHom G.X.hom`, it obtains a chart
cover `j`, with `hj : ∀ k, IsOpenChart (j k)` and
`hc : CoversFieldPoints j`. It then applies
`OpenCharts.exists_smooth_universal j hj (hasEffectiveAdmissibleDescent G) hc`.

That theorem constructs the moduli scheme. By effective descent, the total
presheaf of admissible subgroups is a Zariski sheaf. The charts are
relatively representable open immersions, and the field coverage gives local
surjectivity of their coproduct. Mathlib's
`Scheme.LocalRepresentability.representableBy` then represents the sheaf by
the scheme glued from the charts. Its universal section gives the base map
`M → S` and the actual universal closed torus family. Universality is the
representing bijection on every relative test scheme over `S`, nonaffine
and nonreduced tests included. Smoothness of `M → S` is checked locally on
the glued open cover by the chart schemes, each of which is smooth over `S`
by `IsOpenChart`.

No representing scheme, gluing theorem or representability theorem is
assumed beyond Mathlib and the published Library. The only hypothesis of the
proved implication is `ChartCoverStatement.{u}`.
