# The idele measure `d^×a` and the norm

Module `Langlands.Global.RankinSelberg.EqualAnalyticIdeles`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

Here `𝔸^× = GL_1(𝔸)` is `Points F 1`, `F^×` is the rational subgroup `ideleRational F`, `D₁`
is its Library fundamental domain `ideleDomain F`, and `ideleMeasure F` is the measure of
`EqualIntegrals`. That measure is Haar measure divided by `ideleSlabVolume F`, the quotient
volume of the slab `F^× \ {1 ≤ |a| < e}`.

## Results

- The imported `RankinSelbergGlobal.points_one_mul_comm`: `GL_1(𝔸)` is commutative.
- `normScale y` is the idele with every archimedean component `exp (y / [F:ℚ])` and finite part
  `1`. It is a continuous homomorphism `ℝ → 𝔸^×` (`normScale_add`, `normScale_zero`,
  `continuous_normScale`) with `|normScale y| = exp y` (`detNorm_normScale`).
- `ideleSlabVolume_eq`: the slab volume equals `haar(D₁ ∩ {1 ≤ |a| < e})`
  (`preimage_image_mk_of_invariant` identifies preimages of images of invariant sets).
- The imported `RankinSelbergGlobal.ideleSlabVolume_ne_zero` and
  `RankinSelbergGlobal.ideleSlabVolume_ne_top` give the positivity and finiteness of the slab
  volume. These and commutativity are reused from `EqualUnfoldingIdele`.
- `ideleMeasure_slab`: `D₁ ∩ {1 ≤ |a| < e}` has `d^×a`-measure one.
- **`logNormMeasure_eq_volume`**: the image of `d^×a` restricted to `D₁` under
  `logNorm a = log |a|` is Lebesgue measure. The image measure is translation invariant,
  because translating by `normScale y` preserves `d^×a`-measures of invariant sets inside the
  fundamental domain (`ideleMeasure_inter_preimage_normScale`). It gives every interval
  `[a, a + 1)` mass one (`logNormMeasure_Ico`), so it is finite on compact sets. Haar uniqueness
  on `ℝ` (Mathlib `isAddLeftInvariant_eq_smul_of_regular`) and the normalization on `[0, 1)`
  identify it with `volume`.
- Consequences: `ideleMeasure_logNorm_preimage` (`d^×a(D₁ ∩ {log |a| ∈ B}) = vol(B)`),
  `lintegral_logNorm`, `integral_logNorm`, `integrableOn_logNorm_iff`.

## Provenance

The statements are the standard structure of `F^× \ 𝔸^×` (Tate's thesis; Weil, *Basic Number
Theory*). Here they are proved for the Library's concrete measure `ideleMeasure`. The proofs
are internal; the normalization is the one fixed in `EqualIntegrals`.
