# Proof of the separation of right translates by left-finite adelic test functions

Module `Langlands.Global.RightTranslationTestFunctionSeparationProof`.

The theorem `Langlands.Global.rightTranslationTestFunctionSeparation` proves the unchanged
statement `Langlands.Global.RightTranslationTestFunctionSeparationStatement` of
`Langlands.Global.AdelicWavePacketTranslationReduction`. It uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

Notation: `F` is a number field. `G` is an affine group scheme over `F`, locally of finite type
and connected reductive. `H = G(𝔸)` with its Haar measure `μH = Measure.haar`, and
`Γ = rationalSubgroup F G`. `Q = RationalQuotient F G = Γ \ H` carries
`μQ = rationalQuotientHaarMeasure F G`, which is by definition the measure
`LeftCosetSpace.discreteQuotientMeasure Γ _ Measure.haar` of the statement. `y g` denotes
`LeftCosetSpace.rightTranslate Γ g y`. The data are `f ∈ L²(Q)` and a left `Γ`-invariant
`Θ : H → ℂ` with `θ(y) = Θ(y.out)` in `L²(Q)`. Neither `f` nor `Θ` is assumed continuous or
Borel. The hypothesis is `∫ f(y) conj (R(φ)Θ(y.out)) dμQ = 0` for every `φ` with
`IsLeftFiniteTestFunction F G K_∞ φ`, where `K_∞ = K.comap (ofInfinite F G)` and `R(φ)` is
`AdelicGroupPoints.rightConvolution F G φ`. Of the hypothesis `IsMaximalCompactSubgroup F G K`,
the proof uses only that `K` is compact.

## Route

The translate pairing is

`translatePairing f Θ h = Φ(h) = ∫ f(y) conj Θ(y.out h) dμQ`.

The proof shows that `Φ` is continuous and that `∫ conj φ · Φ dμH = 0` for every test function
`φ`, and deduces `Φ = 0`. The target pairing at `g` equals `Φ(g⁻¹)`.

### Quotient facts (section `Quotient`)

- `rationalQuotient_rightTranslate_eq_mk_out_mul`: `y h = mk(y.out · h)`.
- `leftInvariant_mk_out`: `Θ((mk z).out) = Θ(z)` for left `Γ`-invariant `Θ`, since
  `(mk z).out · z⁻¹ ∈ Γ` (`LeftCosetSpace.mk_eq_mk_iff`).
- `haar_preimage_mk_eq_zero`: a `μQ`-null set has a Haar-null preimage in `H`. Replace the set
  by a measurable null superset `Z'`. By `LeftCosetSpace.quotientMeasure_apply`,
  `μQ(Z') = μH(mk⁻¹ Z' ∩ D)` for the chosen Borel fundamental domain `D`. The set `mk⁻¹ Z'` is
  invariant under left multiplication by `Γ`, so
  `IsFundamentalDomain.measure_zero_of_invariant` gives `μH(mk⁻¹ Z') = 0`.
- `haar_isMulRightInvariant_of_connectedReductive` (from `adelicHaarUnimodularity`) and
  `measurePreserving_rationalQuotient_rightTranslate` (from
  `measurePreserving_rightTranslate_rationalQuotientHaarMeasure`): right translation preserves
  `μQ`. `rationalQuotientRightTranslateEquiv h` packages `y ↦ y h` as a measurable equivalence
  with inverse `y ↦ y h⁻¹`, and `measurePreserving_rationalQuotientRightTranslateEquiv` records
  that it preserves `μQ`.

### Continuity of `Φ` and Fubini (section `Pairing`)

- `translatePairing_eq_inner`: `Φ(h) = ⟪R(h) θ, f⟫` in `L²(Q, μQ)`, where `R` is
  `rationalQuotientL2RightAction`. The representative formula
  `coeFn_rationalQuotientL2RightAction` gives `R(h)θ(y) = θ(mk(y.out h))` almost everywhere. Since
  `y ↦ y h` preserves `μQ`, almost-everywhere equalities may be composed with it. Then
  `θ(mk(y.out h)) = Θ(y.out h)` by `leftInvariant_mk_out`, and `RCLike.inner_apply` gives the
  integrand `f · conj (R(h)θ)`.
- `continuous_translatePairing`: `Φ` is continuous, by the joint continuity
  `continuous_rationalQuotientL2RightAction` of the right regular representation and the
  continuity of the inner product.
- `borelRep`: a strongly measurable representative `AEStronglyMeasurable.mk` of an `L²`
  function. Write `θ₀ = borelRep hθ` and `f₀ = borelRep hf`.
- `ae_leftInvariant_eq_borelRep`: for every `x ∈ H`, `Θ(x h) = θ₀(mk(x h))` for almost every
  `h`. The exceptional set is the preimage under `h ↦ x h` of `mk⁻¹{θ ≠ θ₀}`. That set is
  Haar-null by `haar_preimage_mk_eq_zero`, and its preimage is null by `measure_preimage_mul`.
- `translatePairing_eq_borelRep`: `Φ(h) = ∫ f₀(y) conj θ₀(y h) dμQ`.
- `integral_mul_conj_rightConvolution`: for continuous compactly supported `φ`,
  `∫ f(y) conj (R(φ)Θ(y.out)) dμQ = ∫ conj φ(h) Φ(h) dμH`. By `ae_leftInvariant_eq_borelRep`,
  `R(φ)Θ(y.out) = ∫ φ(h) θ₀(y h) dμH` for every `y`. Fubini's theorem
  (`integral_integral_swap`) applies to
  `J(y, h) = f₀(y) conj φ(h) conj θ₀(y h)` on `Q × H`. `J` is strongly measurable because the
  action `Q × H → Q` is continuous (`continuous_rationalQuotient_rightTranslate_uncurry`).
  Integrability is checked with `integrable_prod_iff'`. Each slice in `y` is the product of two
  `L²` functions (`MemLp.integrable_mul`; the translate of `θ₀` is in `L²` by
  `MemLp.comp_measurePreserving`). Hölder's inequality (`integral_mul_norm_le_Lp_mul_Lq` with
  exponents `2, 2`) and the invariance of `μQ` bound `∫ |J(y, h)| dμQ` by
  `|φ(h)| ‖f₀‖₂ ‖θ₀‖₂`, which is integrable in `h`.

### Separation (section `Separation`)

`eq_zero_of_forall_leftFiniteTestFunction` proves the following. Let `K` be compact and `Φ`
continuous on `H` with `∫ conj φ · Φ dμH = 0` for every `φ` with
`IsLeftFiniteTestFunction F G K_∞ φ`. Then `Φ = 0`. Fix `h₀` and suppose `Φ(h₀) ≠ 0`; put
`ε = ‖Φ(h₀)‖ / 2`.

1. `C₁ = archimedeanPart K = K ⊓ range (ofInfinite F G)` is compact
   (`isCompact_archimedeanPart`: the range is the closed set `{finite = 1}`), and its elements
   have finite component `1`. Let `ν₁` be its Haar probability `compactHaarProbability`.
2. The set of `l ∈ G(𝔸_f)` with `‖Φ(ofFinite l · h₀) − Φ(h₀)‖ < ε` is a neighbourhood of `1`.
   The basis of compact open subgroups `finiteAdelicGroupCompactOpenBasis` gives a compact open
   subgroup `L` inside it. Let `C₂` be its image under `ofFinite`, with Haar probability `ν₂`.
   Elements of `C₁` and `C₂` commute (`factors_commute`).
3. Test functions. For `w` in `Langlands.CompactRepresentativeWeights.finiteWeights` on `C₁`
   and `ψ ∈ C_c(H)`, put
   `φ = weightedAverage ν₂ 1 (weightedAverage ν₁ w ψ)`
   (`Langlands.Analysis.CompactAverage`). `φ` is continuous and compactly supported. It is
   invariant under left translation by `ofFinite L` (`weightedAverage_mul_left` with the
   constant weight). For `k ∈ K_∞`, the left translate of `φ` by `ofInfinite k` is the image of
   the translate `leftRegular (ofInfinite k)⁻¹ w` under the linear map
   `averageLinearMap ν₂ ∘ₗ weightLinearMap ν₁ ψ`. This uses `weightedAverage_mul_left_of_commute`
   and `weightedAverage_mul_left`. So the span of these translates lies in the image of the
   finite-dimensional orbit span of `w`, and `φ` is a left-finite test function.
4. Duality. Two applications of `integral_conj_weightedAverage_mul`, first over `C₂` and then
   over `C₁`, turn `∫ conj φ · Φ = 0` into `∫ conj ψ · Ψ_w = 0`, where
   `Ψ₁(z) = ∫_{C₂} Φ(c z) dν₂` and `Ψ_w(h) = ∫_{C₁} conj w(c) Ψ₁(c h) dν₁`. Both are continuous
   (`continuous_integral_mul_left`). Since this holds for all `ψ ∈ C_c(H)`,
   `Langlands.Analysis.compactTestSeparation` gives `Ψ_w = 0` almost everywhere, and continuity
   gives `Ψ_w = 0` (`Continuous.ae_eq_iff_eq`).
5. Density. Let `Ξ ∈ C(C₁, ℂ)` be `c ↦ Ψ₁(c h₀)`. The functional `w ↦ ∫ conj w · Ξ dν₁` is
   continuous (`continuous_integral_conj_mul`). It vanishes on `finiteWeights`, which is dense
   by `dense_archimedean_finiteWeights` (module `Langlands.Global.AdelicArchimedeanFiniteWeights`).
   Hence it vanishes at `Ξ` (`Continuous.ext_on`), and `eq_zero_of_integral_conj_mul_self`
   gives `Ξ = 0`. In particular `Ψ₁(h₀) = ∫_{C₂} Φ(c h₀) dν₂ = 0`.
6. Since `ν₂` is a probability measure,
   `Φ(h₀) = ∫_{C₂} (Φ(h₀) − Φ(c h₀)) dν₂`. Every `c ∈ C₂` is `ofFinite l` with `l ∈ L`, so the
   integrand has norm less than `ε`. Thus `‖Φ(h₀)‖ ≤ ε = ‖Φ(h₀)‖ / 2`, which contradicts
   `Φ(h₀) ≠ 0`.

### Assembly (section `Assembly`)

- `translatePairing_eq_zero` combines `continuous_translatePairing`,
  `integral_mul_conj_rightConvolution` (with the continuity and compact support contained in
  `IsLeftFiniteTestFunction`) and `eq_zero_of_forall_leftFiniteTestFunction`.
- `integral_rightTranslate_mul_conj`: substituting `y ↦ y g⁻¹`
  (`MeasurePreserving.integral_comp'` for `rationalQuotientRightTranslateEquiv g⁻¹`) gives
  `∫ f(y g) conj Θ(y.out) dμQ = Φ(g⁻¹)`. Here `(y g⁻¹) g = y`, and
  `Θ((y g⁻¹).out) = Θ(y.out g⁻¹)` by `leftInvariant_mk_out`.
- `rightTranslationTestFunctionSeparation` introduces the data of the statement and chains the
  two results at `g⁻¹`.

## Provenance and comparison with the statement's sketch

The Markdown of `Langlands.Global.AdelicWavePacketTranslationReduction` sketches the proof
through the right invariance of `μQ`, strong continuity of translation (G. B. Folland,
*A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press 2015,
`folland-2015-abstract-harmonic-analysis-second`, Proposition 2.42), Fubini's theorem, and
density of test functions via the Peter–Weyl theorem (Folland, Theorem 5.12). The implemented
proof follows that outline, with two changes.

- It does not prove density of the test functions in `C_c(G(𝔸))`. Instead it moves the two
  averages onto `Φ` by duality. It uses only the uniform density of finite-orbit functions on
  the compact group `K ∩ G(F_∞)`. That density comes from Stone–Weierstrass and the faithful
  representation obtained from a closed linear embedding of `G`, not from the Peter–Weyl
  theorem.
- For the open-subgroup condition of `IsLeftFiniteTestFunction` it averages over one compact
  open subgroup `L` of `G(𝔸_f)`, chosen small by the continuity of `Φ` at `h₀`. The average
  makes the test function invariant under left multiplication by the image `ofFinite L` of `L`
  in `G(𝔸)`. This avoids decomposing the Haar measure of `G(𝔸)` as a product.

The non-measurability of the given `f` and `Θ` is handled as in the "Integrals" paragraph of the
statement's Markdown: Borel representatives on the quotient, with null sets transported to
`G(𝔸)` by the fundamental domain. The proof does not use Eisenstein series.
