# Localizations as filtered colimits, and condition (F2)

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsLocalization`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.Charts`. It is a helper for the chart
construction of `MurreCharts` (the inductive step of Murre's proof of Proposition 2,
Bourbaki exp. 294). All results are standard commutative algebra combined with condition (F2)
of the published module `MurreCriterionStatement`; no source is formalized here.

## Contents

* `DivIndex M`, for a submonoid `M` of a commutative ring `A`: the elements of `M` (a type
  synonym of `M`), preordered by divisibility (`a ≤ b ↔ a.val ∣ b.val`). It is directed
  (`a, b ≤ a * b`) and nonempty, so filtered as a category. `DivIndex.val` and `DivIndex.mk`
  convert to and from `A`.
* `awayMap (h : a ∣ b) : A[1/a] →+* A[1/b]`, the map of `Localization.Away`, with
  `awayMap_algebraMap`, `awayMap_comp_algebraMap`, `awayMap_id`, `awayMap_comp`.
* `awayDiagram M : DivIndex M ⥤ Under (CommRingCat.of A)`, `a ↦ (A → A[1/a])`.
* For an `A`-algebra `B` with `IsLocalization M B` (that is, `B = M⁻¹A`):
  `toLoc M B a : A[1/a] →+* B` (`IsLocalization.Away.lift`), with `toLoc_algebraMap` and
  `toLoc_comp_awayMap`; the cocone `awayCocone M B` with vertex `A → B`.
* `exists_toLoc_eq`: every element of `B` comes from some `A[1/a]` (write it as `r/m` and take
  `a = m`).
* `exists_awayMap_eq_zero`, `exists_awayMap_eq`: an element of `A[1/a]` vanishing in `B`
  vanishes in some `A[1/b]`, `a ∣ b` (if `r/aⁿ ↦ 0` then `c r = 0` for some `c ∈ M`, and
  `b = a c` works); hence two elements with equal images in `B` become equal in some
  `A[1/b]`.
* `awayCoconeIsColimit`: `awayCocone M B` is a colimit cocone, i.e. `M⁻¹A` is the filtered
  colimit of the rings `A[1/a]`, `a ∈ M`. Colimits in `Under A` are detected by the forgetful
  functors to `CommRingCat` and to types (`isColimitOfReflects`; `Under.forget` reflects
  colimits of connected shape), and in types by `Types.FilteredColimit.isColimitOf`, whose two
  hypotheses are the two previous lemmas.
* Section `F2`, for a presheaf `F` on `Over S` with (F1a) `ZariskiSheaf` and (F2)
  `FilteredColimits`, and `h : Spec A ⟶ S`. The functor
  `BaseChange.specOver h ⋙ F` (published in `MurreBaseChangeColimits`) preserves filtered
  colimits by `BaseChange.good_all`, so it maps `awayCocone` to a colimit of types:
  * `exists_eq_of_isLocalization`: every `ζ ∈ F(Spec B)` is the restriction of some element of
    `F(Spec A[1/a])`, `a ∈ M` (`Types.jointly_surjective_of_isColimit`);
  * `exists_eq_of_isLocalization_of_eq`: two elements of `F(Spec A[1/a])` with the same
    restriction to `Spec B` have the same restriction to some `Spec A[1/b]`, `a ≤ b`
    (`Types.FilteredColimit.isColimit_eq_iff'`).
