# Left translation by a normalizing point on `N_m(𝔸) \ GL_m(𝔸)`

Module `Langlands.Global.RankinSelberg.WhittakerQuotientScaling`, namespace
`Langlands.Global.RankinSelbergGlobal.WhittakerQuotientScaling`.

## Content

This is a helper module for the proof of the one-place Iwasawa cell decomposition
`WhittakerCellDecompositionStatement`. `F` is a number field and `m` a natural number.
`μ` is the Library's `whittakerQuotientMeasure F m` on
`WhittakerQuotient F m = N_m(𝔸) \ GL_m(𝔸)`. It is the image, under `toWhittakerQuotient`,
of the quotient Haar measure on `N_m(F) \ GL_m(𝔸)`. The module proves the following.

1. `μ` is locally finite, regular, nonzero and right `GL_m(𝔸)`-invariant.
2. Let `a ∈ GL_m(𝔸)` normalize `N_m(𝔸)`. The left translation
   `N_m(𝔸) g ↦ N_m(𝔸) a g` multiplies `μ` by the Haar modulus of conjugation by `a` on
   `N_m(𝔸)`.
3. For `a = ι_v(ϖ^λ)` that factor is `N(v) ^ (-∑_(i<j) (λ_i - λ_j))`.

### Compactness

- `exists_isCompact_image_mk_eq_univ`: let `H` be a locally compact topological group and
  `Γ ≤ H` a subgroup with `Γ \ H` compact. Then some compact `K ⊆ H` maps onto `Γ \ H`.
- `exists_isCompact_unipotent_reduction`: some compact `C ⊆ N_m(𝔸)` satisfies
  `N_m(𝔸) = N_m(F) C`. For every `n ∈ N_m(𝔸)` there is a `c ∈ C` with `n c⁻¹` in the
  Library's `unipotentRationalImage F m`.

### The measure `μ`

- `toWhittakerQuotient_mk`: `toWhittakerQuotient` sends the class of `x` in
  `N_m(F) \ GL_m(𝔸)` to the class of `x` in `N_m(𝔸) \ GL_m(𝔸)`.
- `isLocallyFiniteMeasure_whittakerQuotientMeasure`: `μ` is locally finite.
- `toWhittakerQuotient_rightTranslate`: `toWhittakerQuotient` commutes with right
  translation by `g ∈ GL_m(𝔸)`.
- `measurePreserving_rightTranslate`: right translation by `g` preserves `μ`.
- `whittakerQuotientMeasure_ne_zero`: `μ ≠ 0`.
- `regular_whittakerQuotientMeasure`: `μ` is regular.
- `mulEquivHaarChar_conjugation`: `GL_m(𝔸)` is unimodular. The Haar character of
  `conjugation a` on `GL_m(𝔸)` is `1`.

### Left translation

- `leftShift F m a`: the map `q ↦ N_m(𝔸) (a · q.out)` on `N_m(𝔸) \ GL_m(𝔸)`, through the
  chosen representative `q.out`. It is defined for every `a`. The statement module's
  `shift λ` is `leftShift F m (localPoint F m v (torus ϖ λ))` by definition.
- `leftShiftHomeomorph a hα`: for `a` normalizing `N_m(𝔸)`, a homeomorphism of
  `N_m(𝔸) \ GL_m(𝔸)`. The hypothesis
  `hα : ∀ x, conjugation a x ∈ N_m(𝔸) ↔ x ∈ N_m(𝔸)` states that `a` normalizes `N_m(𝔸)`.
  The homeomorphism is the Library's `QuotientIntegration.quotientAutomorphism` of
  `conjugation a`, which sends `N_m(𝔸) x` to `N_m(𝔸) a x a⁻¹`, followed by right
  translation by `a`.
- `coe_leftShiftHomeomorph`: as a function, `leftShiftHomeomorph a hα` is
  `leftShift F m a`.
- `leftShift_mk`: `leftShift F m a (N_m(𝔸) x) = N_m(𝔸) a x`, for `a` normalizing
  `N_m(𝔸)` and any representative `x`.
- `leftShiftHomeomorph_symm_mk`: the inverse sends `N_m(𝔸) x` to `N_m(𝔸) a⁻¹ x`.

### Scaling

- `map_leftShift`: **scaling of `μ`.** For `a` normalizing `N_m(𝔸)`,
  `Measure.map (leftShift F m a) μ = δ • μ`. Here `δ` is the Haar character
  `mulEquivHaarChar` of the Library's `QuotientIntegration.subgroupAutomorphism`, the
  restriction of `conjugation a` to `N_m(𝔸)`.
- `map_leftShift_localPoint_torus`: **the measure `μ` under `ι_v(ϖ^λ)`.** Let `v` be a
  finite place and `ϖ` a uniformizer for `WhittakerCellAdelicScaling.valuation F v`.
  That valuation is, by definition, `Valued.v` on `F_v`. Then for every `λ ∈ ℤ^m`,
  `Measure.map (leftShift F m (localPoint F m v (torus ϖ λ))) μ =
  N(v) ^ (-modulusExponent λ) • μ`, where `N(v) = Ideal.absNorm v.asIdeal` as an element
  of `ℝ≥0`.
- `integrable_comp_leftShift`: let `a` normalize `N_m(𝔸)` with
  `Measure.map (leftShift F m a) μ = δ • μ` for some `δ ∈ ℝ≥0`. If `f` is `μ`-integrable,
  so is `f ∘ leftShift F m a`.
- `setIntegral_comp_leftShift`: under the same hypotheses, for every set `U` and every
  `f : N_m(𝔸) \ GL_m(𝔸) → ℂ`,
  `∫_U f(leftShift F m a q) dμ(q) = δ · ∫_(L(U)) f dμ`. Here
  `L(U) = (leftShiftHomeomorph a hα).symm ⁻¹' U` is the image of `U` under the left
  translation.

## Proofs

`exists_isCompact_image_mk_eq_univ`: choose a compact neighbourhood `U_x` of every
`x ∈ H`. The images of the interiors are open, because the quotient map is open, and they
cover the compact space `Γ \ H`. Finitely many of them cover it, and the union of the
corresponding `U_x` is the required compact set.

`exists_isCompact_unipotent_reduction`: `N_m(F) \ N_m(𝔸)` is compact by the Library's
`Unfolding.compactSpace_unipotentRationalQuotient`. Apply the previous lemma, and read the
equality of classes as membership of `n c⁻¹` in the rational subgroup
(`Unfolding.mem_unipotentRationalImage_iff`).

`isLocallyFiniteMeasure_whittakerQuotientMeasure`: let `q = N_m(𝔸) x`. Take a compact
neighbourhood `V` of `x` and the compact `C` of the previous lemma. The image `O` of the
interior of `V` is an open neighbourhood of `q`. Let `z ∈ GL_m(𝔸)` have class in
`toWhittakerQuotient ⁻¹' O`. Then `z y⁻¹ ∈ N_m(𝔸)` for some `y ∈ V`, so
`z y⁻¹ = γ c` with `γ ∈ N_m(F)` and `c ∈ C`. Hence `N_m(F) z = N_m(F) c y` lies in the
image of the compact set `C · V`. That image has finite measure for the quotient Haar
measure, which is locally finite (the Library's
`LeftCosetSpace.isLocallyFiniteMeasure_haarQuotientMeasure`). So `μ(O) < ∞`.

`measurePreserving_rightTranslate`: Haar measure on `GL_m(𝔸)` is right invariant
(`Automorphic.OperatorDeterminantSlice.haar_isMulRightInvariant`). So right translation
preserves the quotient Haar measure on `N_m(F) \ GL_m(𝔸)`
(`LeftCosetSpace.measurePreserving_rightTranslate_haarQuotientMeasure`), and it commutes
with `toWhittakerQuotient`.

`whittakerQuotientMeasure_ne_zero`: the image of a nonzero measure is nonzero
(`LeftCosetSpace.haarQuotientMeasure_ne_zero`).

`regular_whittakerQuotientMeasure`: apply Mathlib's
`Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` to the locally finite `μ`. That
result states that a locally finite Borel measure on a `σ`-compact pseudometrizable space
is regular. The Library's instances make `N_m(𝔸) \ GL_m(𝔸)` such a space.

`mulEquivHaarChar_conjugation`: conjugation is a left translation followed by a right
translation. Haar measure on `GL_m(𝔸)` is invariant under both, and the Library's
`HarmonicAnalysis.mulEquivHaarChar_eq_of_smul_map` gives the character `1`.

`coe_leftShiftHomeomorph`, `leftShift_mk`, `leftShiftHomeomorph_symm_mk`: the composite
sends `N_m(𝔸) x` to `N_m(𝔸) a x a⁻¹ a = N_m(𝔸) a x`. Applied to `x = q.out` this is
`leftShift`, and the formula for the inverse follows.

`map_leftShift`: `N_m(𝔸)` is closed in `GL_m(𝔸)`. Haar measure on `N_m(𝔸)` is right
invariant, because `N_m(F) \ N_m(𝔸)` is compact
(`AdelicSubgroupPoints.haar_isMulRightInvariant_of_compactRationalQuotient`). The Library's
`QuotientIntegration.compatibleMeasureExists` gives a measure `ν₀` on
`N_m(𝔸) \ GL_m(𝔸)` compatible with the two Haar measures. `ν₀` is regular, nonzero and
right invariant. So is `μ`, by the lemmas above. The Library's
`QuotientIntegration.exists_pos_smul_eq_of_rightInvariant_quotient` then gives
`μ = C · ν₀` for a constant `C > 0`. For the compatible `ν₀`, the Library's
`IsCompatible.map_quotientAutomorphism` gives
`Measure.map (quotientAutomorphism (conjugation a)) ν₀ = (δ_N / δ_G) • ν₀`. Here `δ_N`
is the character of the restriction to `N_m(𝔸)`, and `δ_G = 1` by
`mulEquivHaarChar_conjugation`. `leftShift F m a` is the quotient automorphism followed
by right translation by `a`, which preserves `μ`. Composing the two images and cancelling
`C` gives `Measure.map (leftShift F m a) μ = δ_N • μ`.

`map_leftShift_localPoint_torus`: combine `map_leftShift` with
`UnipotentConjugationModulus.conj_localPoint_torus_mem_iff`, which shows that `ι_v(ϖ^λ)`
normalizes `N_m(𝔸)`, and with
`UnipotentConjugationModulus.mulEquivHaarChar_conj_localPoint_torus`, which gives
`δ_N = N(v) ^ (-modulusExponent λ)`.

`integrable_comp_leftShift`, `setIntegral_comp_leftShift`: `leftShiftHomeomorph a hα` is
a measurable equivalence whose underlying function is `leftShift F m a`. Mathlib's
`integrable_map_equiv` and `MeasurableEmbedding.setIntegral_map` transport integrability
and the set integral to the image measure `δ • μ`. The preimage of `L(U)` under the left
translation is `U`. The factor `δ` comes out through `Measure.restrict_smul` and
`integral_smul_measure`.

## Provenance

This is the measure-theoretic step behind Cogdell's local formula
`dh = dn δ_B⁻¹(ϖ^J) dk` on `N_m \ GL_m = ⊔_J N_m ϖ^J K_m` (J. W. Cogdell, *Lectures on
L-functions, converse theorems, and functoriality for GL_n*, Fields lectures 2003,
Lecture 7 §3, p.57). There the factor `δ_B⁻¹(ϖ^J)` comes from moving `ϖ^J` past the
unipotent variable. The Lean statements are global, on `N_m(𝔸) \ GL_m(𝔸)` for
`whittakerQuotientMeasure`, and the proofs are internal to this project. The proofs use
the Library's uniqueness of right-invariant quotient measures and its scaling of
compatible quotient measures under automorphisms. The modulus itself comes from
`UnipotentConjugationModulus`.
