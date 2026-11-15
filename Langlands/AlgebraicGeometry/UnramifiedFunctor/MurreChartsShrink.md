# Shrinking a chart: unramified and étale

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsShrink`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.Charts`. Part of the chart construction of
`MurreCharts`, following the proof of Murre's Proposition 2 (Bourbaki exp. 294, printed
pp.252–253): a point of `F` over `s ∈ Spec R` lies in a chart `U → F` étale at the points over
`s`, which by Lemma 2 is étale on a neighbourhood.

## Setting (section `Setup`)

`s : Spec R`; `e` represents the base change of `F` to `Spec 𝒪_{Spec R, s}` by `Y`;
`j : Over.mk t ⟶ Y` is an open immersion from `Spec B`, `t : Spec B ⟶ Spec 𝒪_s` with
`t ≫ fromSpecStalk s` the structure morphism of `ovR R B`; this gives
`ξ_B = elemEquiv _ e (ovR R B) t ht j ∈ F(Spec B)`. Further `A` is an `R`-algebra, `B = M⁻¹A`
for a submonoid `M` of `A`, and `ξ ∈ F(Spec A)` restricts to `ξ_B` (hypothesis `hξ`).

## Contents

* `resA ξ a ∈ F(Spec A[1/a])`, the restriction of `ξ`; `resA_awayMapₐ` (compatibility for
  `a ∣ b`); `unit_of_dvd`, `algebraMap_notMem_comap` (points of `Spec A[1/b]` map into
  `D(n) ⊆ Spec A[1/a]` when `a ∣ b` and `n ∣ b`).
* `map_toLocₐ_resA`: for `a ∈ M`, `resA ξ a` restricts to `ξ_B` on `Spec B`.
* `infinitesimallyEtaleAt_resA`: for `a ∈ M`, `resA ξ a` is infinitesimally étale at every
  point of `Spec A[1/a]` whose prime is disjoint from `M`. A morphism from the spectrum of a
  local artinian ring to `Spec A[1/a]` with that image inverts `M`, so factors uniquely
  through `Spec B` (`IsLocalization.lift`); on `Spec B` the element is `ξ_B`, infinitesimally
  étale everywhere by `infinitesimallyEtaleAt_elemEquiv` (with `fromSpecStalk_factor`);
  `infinitesimallyEtaleAt_of_factor` concludes.
* `exists_etale`: for `a ∈ M`, if the étale locus of `resA ξ a` is open (this is where Murre's
  Lemma 2 is used, as a hypothesis), then some `n ∈ M` makes `resA ξ b` infinitesimally étale
  at every point for every `b` divisible by `a n`. The locus contains all primes disjoint from
  `M`, hence some `D(n)` (`exists_mem_basicOpen_subset`), and `Spec A[1/b]` maps into `D(n)`
  by an open immersion (`infinitesimallyEtaleAt_restrict`).
* `exists_unramified` (section `Unramified`): if `A` is of finite type over `R` and `M⁻¹A` is
  formally unramified over `R`, some `m₁ ∈ M` makes `A[1/a]` formally unramified over `R` for
  all `a` divisible by `m₁` (unramified locus, `MurreChartsAlgebra`).
