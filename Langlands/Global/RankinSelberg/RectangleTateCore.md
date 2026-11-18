# Coordinates on adelic rectangular matrices and uniqueness of Haar measure

Helper module for the proof of `Langlands.Global.RankinSelbergGlobal.RectangleTateStatement`
(premise C of `ArchimedeanFactorizationReduction`; the final assembly is in
`RectangleTateProof.md`). Namespace: `Langlands.Global.RankinSelbergGlobal.RectangleTate`.

The mathematics is Tate's computation of adelic Haar measure (Tate's thesis, §4, in
Cassels–Fröhlich 1967). The measure on `𝔸` that gives `𝔸 / F` volume one is the product of
the self-dual local measures, because the self-dual measure of `𝔸` has covolume one. The
present module does the measure-theoretic part for `k × m` matrices, for arbitrary Haar
measures on the local factors. It proves:

1. the image of the Library's covolume-one measure `rectangleMeasure F k m` under a
   coordinate isomorphism is `c` times a product of Haar measures (uniqueness of Haar
   measure), so integrals of products of local functions factor with the constant `c`
   (`integral_indicator_rect`);
2. `c = 1` as soon as an explicit fundamental domain of `M_(k,m)(F)` has product measure one
   (`scalar_eq_one`).

The route is internal; it does not follow a specific text. The normalization hypothesis of
`scalar_eq_one` is discharged in `RectangleTateProof` from the Library's Tamagawa
normalization.

Notation: `F` is a number field, `S` a finite set of finite places, `k m : ℕ`, `F_v` the
completion `FiniteCompletion F v`, `𝒪_v` its ring of integers, `φ` the Mathlib isomorphism
`InfiniteAdeleRing.ringEquiv_mixedSpace F` from the infinite adeles to the mixed space
`ℝ^(r₁) × ℂ^(r₂)`.

## Local instances

The finite completions carry their valued (completion) topology and the Borel σ-algebra
(`completionMeasurableSpace`, `completionBorelSpace`). They are second countable
(`finiteCompletion_secondCountableTopology`) and locally compact, because `𝒪_v` is a compact
open subgroup (`isCompact_adicCompletionIntegers`). `M_(k,m)(𝔸)` carries the Borel σ-algebra,
as in `WhittakerIntegrals.rectangleMeasure`. Instance search does not find several product
instances (Borel, second countable, measurable addition) on the coordinate space below, so
they are stated one by one as local instances. All of them hold by `inferInstance` or
`Prod.borelSpace` once the factors are available.

## The finite adeles away from `S` and the coordinates `theta`

* `OffAdeles F S` is the restricted product of the `F_v`, `v ∉ S`, with respect to the `𝒪_v`,
  written exactly as the second factor of `RestrictedProduct.splitFiniteHomeomorph`. It is a
  topological group, locally compact (Mathlib instances, using the local fact that every
  `𝒪_v` is open) and second countable (`restrictedProduct_secondCountableTopology`).
* `split F S : 𝔸_f ≃ₜ (∏_(v ∈ S) F_v) × 𝔸^S` is `splitFiniteHomeomorph` for the predicate
  `· ∈ S`. It is additive (`split_add`, by `rfl`); its components are the evaluations
  (`split_apply_fst`, `split_apply_snd`).
* `TateSpace F S k m = ((RealPart × ComplexPart) × LocalPart) × OffPart` with
  `RealPart = ∏_(v real) (Fin k → Fin m → ℝ)`, `ComplexPart = ∏_(w complex) (Fin k → Fin m → ℂ)`,
  `LocalPart = ∏_(v ∈ S) (Fin k → Fin m → F_v)`, `OffPart = Fin k → Fin m → 𝔸^S`. Iterated
  function types are used instead of `Matrix`, so that Mathlib's product instances apply.
* `theta F S k m : M_(k,m)(𝔸) ≃ₜ+ TateSpace F S k m` sends `x` to
  `(((v, i, j) ↦ φ(x_ij,∞)_v, (w, i, j) ↦ φ(x_ij,∞)_w), (v, i, j) ↦ (x_ij)_v), (i, j) ↦ split(x_ij,f).2`.
  The inverse rebuilds each entry from `φ⁻¹` and `split⁻¹`. Additivity follows from that of
  `φ` and `split`, continuity from `continuous_infiniteAdeleCoordinates(_symm)` and the
  continuity of `split`. By construction the real, complex and `S` components of `theta x`
  are the Library's `realRectCoordinates`, `complexRectCoordinates` and `localRectCoordinates`
  of `x` (definitionally), and `(theta x).2 i j v = finiteProjection F v (x i j)`
  (`theta_apply_snd`).

## The compact open subgroup `M_(k,m)(∏_(v ∉ S) 𝒪_v)`

* `offIntegers F S ⊆ 𝔸^S` is the set of elements integral at every place. It is the range of
  the structure map from `∏_(v ∉ S) 𝒪_v` (`RestrictedProduct.range_structureMap`), hence compact
  (`isCompact_offIntegers`), and it is open (`isOpen_offIntegers`).
* `offSet F S k m = M_(k,m)(offIntegers)` is compact and open, and it contains `0`.
  `offCompacts` packages it as a compact set with nonempty interior.
* `offMeasure F S k m = Measure.addHaarMeasure (offCompacts F S k m)` is the Haar measure of
  `OffPart` with `offMeasure (offSet) = 1` (`offMeasure_offSet`).

## Uniqueness of Haar measure

* `productMeasure μR μC ν`, for measures `μR v` on `ℝ`, `μC w` on `ℂ` and `ν v` on `F_v`
  (`v ∈ S`), is
  `((pi_v pi_i pi_j μR v).prod (pi_w pi_i pi_j μC w)).prod (pi_v pi_i pi_j ν v)` followed by
  `.prod offMeasure`. If all `μR v`, `μC w`, `ν v` are additive Haar measures, it is an additive
  Haar measure (`productMeasure_isAddHaarMeasure`, through `isAddHaarMeasure_pipi` and
  `isAddHaarMeasure_pipipi` for iterated finite products).
* Assume `CompactSpace (AdeleQuotient F)`. The image `Measure.map theta (rectangleMeasure F k m)` is an
  additive Haar measure (`map_theta_isAddHaarMeasure`; `rectangleMeasure` is Haar by the
  Library's `Unfolding.rectangleMeasure_isAddHaarMeasure'`).
* `scalar μR μC ν : ℝ≥0` is `Measure.addHaarScalarFactor` of the image measure with respect to
  `productMeasure μR μC ν`. `map_theta_eq`: the image measure is `scalar • productMeasure`
  (Mathlib's `Measure.isAddLeftInvariant_eq_smul`; the coordinate space is locally compact and
  second countable).
* `integral_theta`: `∫ G(theta x) d rectangleMeasure = scalar · ∫ G d productMeasure` for every
  `G : TateSpace → ℂ` (`MeasurableEmbedding.integral_map`, `integral_smul_measure`).

## Integrals of products of local functions

For `hR v : M_(k,m)(ℝ) → ℂ`, `hC w : M_(k,m)(ℂ) → ℂ` and `hS v : M_(k,m)(F_v) → ℂ`:

* `tensor hR hC hS z = ∏_v hR v (z_v) · ∏_w hC w (z_w) · ∏_(v ∈ S) hS v (z_v) · 1_offSet(z_off)`.
* `mem_rectIntegralOutside_iff`: `x ∈ rectIntegralOutside F k m S` if and only if
  `(theta x).2 ∈ offSet` (both say that every entry of `x` is integral at every `v ∉ S`).
* `indicator_eq_tensor`: the integrand of `RectangleTateStatement` at `x` equals
  `tensor hR hC hS (theta x)`.
* `integral_tensor`: `∫ tensor d productMeasure` is the product of the local integrals
  `∏_v ∫ hR v d(pi_i pi_j μR v) · ∏_w ∫ hC w d(pi_i pi_j μC w) · ∏_(v ∈ S) ∫ hS v d(pi_i pi_j ν v)`.
  The proof applies `integral_prod_mul` three times and `integral_fintype_prod_eq_prod` three
  times. It uses `∫ 1_offSet d offMeasure = 1`. No integrability hypothesis is needed: both
  lemmas hold for all functions, and both sides are `0` in the non-integrable cases.
* `integral_indicator_rect`: the left side of `RectangleTateStatement` equals
  `scalar μR μC ν` times the product of the local integrals above. It combines `integral_theta`,
  `indicator_eq_tensor` and `integral_tensor`.

## A fundamental domain and the value of the scalar

* `integerIdeal F` is the fractional ideal `Hecke.latticeIdeal 0`. By
  `Hecke.mem_latticeIdeal_iff` and `valuedAdicCompletion_eq_valuation'`, it consists of the
  elements of `F` integral at every finite place (`mem_integerIdeal_iff`).
* `archDomain F` is the parallelepiped `ZSpan.fundamentalDomain` of the basis
  `mixedEmbedding.fractionalIdealLatticeBasis F (integerIdeal F)` of the mixed space.
* `adeleDomain F = {a ∈ 𝔸 | φ(a_∞) ∈ archDomain F, a_v ∈ 𝒪_v for all finite v}`.
  - `exists_add_mem_adeleDomain`: every adele has a translate by `F` in `adeleDomain`. First
    choose `x ∈ F` with `a_f − x` integral (the Library's `exists_sub_mem_integralFiniteAdeles`).
    Then move the infinite component into `archDomain` by an element `δ` of the lattice
    (`ZSpan.exist_unique_vadd_mem_fundamentalDomain`, `mem_span_fractionalIdealLatticeBasis`).
    `δ` lies in `integerIdeal F`, so it does not change integrality.
  - `eq_of_add_mem_adeleDomain`: such a translate is unique. If `γ₁ + a` and `γ₂ + a` lie in
    `adeleDomain`, then `γ₁ − γ₂` is integral everywhere, so its mixed embedding lies in the
    lattice. Uniqueness in `ZSpan.exist_unique_vadd_mem_fundamentalDomain` makes the
    embedding `0`, and `mixedEmbedding` is injective.
* `rectAdeleDomain F k m = M_(k,m)(adeleDomain F)`. `existsUnique_add_mem_rectAdeleDomain`
  (entrywise) and `measurableSet_rectAdeleDomain` give
  `isAddFundamentalDomain_rectAdeleDomain`: it is a fundamental domain of the Library's
  `Unfolding.rectLattice F k m = M_(k,m)(F)` for every measure. Comparing with the Library's
  fundamental domain `Unfolding.rectDomain` (`IsAddFundamentalDomain.measure_eq`,
  `Unfolding.rectangleMeasure_rectDomain`) gives
  `rectangleMeasure F k m (rectAdeleDomain F k m) = 1` (`rectangleMeasure_rectAdeleDomain`).
* `theta_preimage_eq`: `rectAdeleDomain` is the preimage under `theta` of the product set
  `(archSet ×ˢ localSet) ×ˢ offSet`. Here `archSet` is the set of pairs whose `(i, j)` entries
  `((v ↦ p₁ v i j), (w ↦ p₂ w i j))` lie in `archDomain F`, and
  `localSet = ∏_(v ∈ S) M_(k,m)(𝒪_v)`. A place outside `S` is handled by `offSet`, a place in
  `S` by `localSet`.
* `productMeasure_tateSet`: the product measure of this set is
  `λ(archDomain F)^(km) · (∏_(v ∈ S) ν v (𝒪_v))^(km)` with `λ = (pi μR).prod (pi μC)` on the
  mixed space. The archimedean factor uses `archSet_eq` and the measure-preserving
  rearrangement `measurePreserving_rearrange` of `RectangleTateMeasure`. The other factors use
  `Measure.pi_pi` and `offMeasure_offSet`.
* `scalar_eq_one`: if `λ(archDomain F) · ∏_(v ∈ S) ν v (𝒪_v) = 1`, then `scalar μR μC ν = 1`.
  Indeed `1 = rectangleMeasure (rectAdeleDomain) = scalar · productMeasure (archSet ×ˢ …)
  = scalar · (λ(archDomain F) · ∏ ν v (𝒪_v))^(km) = scalar` by `map_theta_eq`.
