# The covolume-one measure on `𝔸^n` as a product measure

Module `Langlands.Global.RankinSelberg.EqualAnalyticProduct`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

Under `𝔸^n ≅ (F_∞)^n × (𝔸_f)^n`, with `F_∞` the mixed space, the covolume-one measure is a positive
multiple of the product of Lebesgue measure and a Haar measure of `(𝔸_f)^n`. Integrals of tensors
`g(x_∞) h(x_f)` therefore factor.

## Provenance

Internal; uniqueness of Haar measure (Mathlib `Measure.isAddLeftInvariant_eq_smul`), following
the pattern of the Library module `Langlands.Global.AdelicScalarHaarChar`.

## Declarations

- Shortcut instances `mixedSpace_sigmaFinite`, `mixedSpace_isAddHaarMeasure`,
  `mixedSpace_measurableAdd`, `mixedSpace_borelSpace`, `archRow_borelSpace`, `archRow_sigmaFinite`,
  `archRow_isAddHaarMeasure` cover the mixed space and its powers. Without them, instance search
  for Lebesgue measure on `Fin n → mixedSpace F` fails.
- `ArchRow F n = Fin n → mixedSpace F` and `FinRow F n = Fin n → FiniteAdeles F`.
- `rowSplit F n : RowVector F n ≃ₜ+ ArchRow F n × FinRow F n` sends `x` to
  `(archimedeanCoordinates F n x, finiteCoordinates F n x)`. It uses the Library's continuous
  ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace` and its inverse
  (`continuous_infiniteAdeleCoordinates(_symm)`).
- `rowProductMeasure F n = volume.prod addHaar`, an additive Haar measure.
- `rowConstant F n : ℝ≥0` with `map_rowSplit_rectangleMeasure`: the image of
  `rectangleMeasure F 1 n` under `rowSplit` is `rowConstant F n • rowProductMeasure F n`.
  `rowConstant_ne_zero` holds.
- `integral_rect_eq`, `lintegral_rect_eq`, `integrable_rect_iff`: integrals and integrability
  transported through `rowSplit`.
- `integrable_rect_tensor` and `integral_rect_tensor`: for `g` integrable on `(F_∞)^n` and `h`
  integrable on `(𝔸_f)^n`, the function `x ↦ g(x_∞) h(x_f)` is integrable, and its integral is
  `rowConstant • (∫ g) (∫ h)`.
