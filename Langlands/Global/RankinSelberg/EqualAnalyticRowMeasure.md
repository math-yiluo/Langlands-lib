# The covolume-one Haar measure on adelic row vectors

Module `Langlands.Global.RankinSelberg.EqualAnalyticRowMeasure`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

This module is the first supporting unit of the harmonic analysis on `𝔸^n` used for the proof of
`Langlands.Global.RankinSelbergGlobal.EqualAnalyticStatement` (Cogdell 2004, Theorem 2.2). It
shows that the Library's measure `rectangleMeasure F 1 n` on row vectors `𝔸^n = M_{1×n}(𝔸)` is an
additive Haar measure. It also shows that the rational row vectors `F^n` have a fundamental domain
of measure one, and that integrals over `𝔸^n` unfold to integrals over the compact quotient
`(𝔸/F)^n`.

## Provenance

Internal. The facts are standard (Tate's thesis, §4.1, where the measure of `𝔸/F` is
normalized to one). Here they are derived from the definitions already in the Library:
`rectangleMeasure F 1 n` is the image of `GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure` (Haar
measure on the block unipotent subgroup scaled by the inverse mass of its rational quotient). The
quotient measure `matrixQuotientHaar F 1 n` is the Haar probability on `(𝔸/F)^n`.

## Declarations

- `t2Space_finiteAdeles`, `t2Space_infiniteAdeles`, `t2Space_adeles`: the adele rings are Hausdorff.
- `RowGroup F n`: the block unipotent subgroup of `GL_{1+n}(𝔸)` whose coordinates are the row
  vectors. `rowHomeomorph F n : RowGroup F n ≃ₜ RowVector F n` is its coordinate homeomorphism
  (Library `adelicCoordinates` followed by `toAdd`), with `rowHomeomorph_mul` and `rowHomeomorph_symm_add`.
- `rowLattice F n`: the additive subgroup `F^n ⊆ 𝔸^n` (the range of entrywise `algebraMap`). It is
  countable (`rowLattice_countable`). `rowHomeomorph_mem_rowLattice_iff` says it is the image of the
  principal subgroup.
- `rectangleMeasure_eq_map`, `normalizedBlockHaarMeasure_eq`: unfolding of the definitions.
- `rectangleMeasure_isAddHaarMeasure` (instance): `rectangleMeasure F 1 n` is an additive Haar
  measure. It is a positive finite multiple of the image of a Haar measure under a homeomorphic
  group isomorphism. Left invariance follows from `rowHomeomorph_mul`.
- `rowDomain F n`: the image of the Library's Borel fundamental domain of the principal subgroup.
  `existsUnique_add_mem_rowDomain`: every row vector has exactly one translate by `F^n` in
  `rowDomain`. `isAddFundamentalDomain_rowDomain`: it is an additive fundamental domain for every
  measure.
- `rectangleMeasure_rowDomain`: `rectangleMeasure F 1 n (rowDomain F n) = 1`. The normalizer is
  the inverse of the quotient Haar mass, which equals the Haar measure of the fundamental domain.
- `map_matrixQuotientMap_restrict`: the image of `rect` restricted to `rowDomain` under the
  reduction map `𝔸^n → (𝔸/F)^n` is `matrixQuotientHaar F 1 n`. This is the Library theorem
  `map_quotientHomeomorph_normalizedRationalQuotientHaarMeasure`, unfolded.
- `integral_eq_integral_periodization`: if `f` is integrable on `𝔸^n` and for every `v` the family
  `c ↦ f(c + v)` over `c ∈ F^n` has sum `P(v mod F^n)` with `P` a.e.-strongly measurable, then
  `∫_{𝔸^n} f = ∫_{(𝔸/F)^n} P`. `lintegral_eq_lintegral_periodization` is the nonnegative version.
  The proof uses Mathlib's `IsAddFundamentalDomain.integral_eq_tsum'` and `integral_tsum`, and
  then the image measure.
