# Proof of the finite compact comparison for `A^2_P` and the Levi pairings (3.7)

`Langlands.Global.finiteCompactPairingComparison` proves
`Langlands.Global.FiniteCompactPairingComparisonStatement`, stated in
[`AdelicFiniteCompactPairingComparisonStatement`](AdelicFiniteCompactPairingComparisonStatement.md),
with exactly its type. It adds no hypothesis: the statement is for every standard parabolic
`P = P_J` of a compatible family `𝓕` and every pair of maximal compact subgroups `K₁`, `K₂` of
`G(𝔸)` with `P(𝔸) Kᵢ = G(𝔸)` and the same infinite projection. Neither compact is assumed to be
in good position. The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

Notation: `ι = map F P G p : P(𝔸) → G(𝔸)`, `ι_M = map F M G (l ≫ p)`,
`Δ = H_P^{K₁} - H_P^{K₂}`, `φ_v = cut v φ = 1_{Δ = v} φ`, `Γ = U(𝔸) M(F)`
(`parabolicQuotientSubgroup`), `[M]^1 = M(F) \ M(𝔸)^1` (`NormOneRationalQuotient F M`) with
`normOneRationalQuotientHaarMeasure`, and `δ_P(q)` the idele norm of `det(Ad(q) | Lie P)`,
so that `δinv q = δ_P(q)⁻¹` (`IwasawaCompatibleMeasure.parameterPower_neg_modulusParameter`).

## Assertions 1 and 2: finite range and clopen fibres

`IsMaximalCompactSubgroup.isOpen_intersection_of_infinite_eq` gives that `K₁ ∩ K₂` is open in
`K₁`. Then `IsIwasawaCompact.finite_range_height_sub` gives the finite range of `Δ` (the finite
set is `(Set.range Δ).Finite.toFinset`), and
`IsIwasawaCompact.exists_parameterTwist_clopen_decomposition` gives the clopen fibres. Both are
in the module `AdelicEisensteinFiniteCompactChangeProof`.

Two facts are used throughout: `Δ(ι(q) g) = Δ(g)` for `q ∈ P(𝔸)`
(`IsIwasawaCompact.height_map_mul` for both heights), and `Γ ≤ ι(P(𝔸))`, so `Δ` and every cut
`φ_v` of a left `Γ`-invariant `φ` are left `Γ`-invariant.

## Assertion 3: the inducing forms

Let `φ` satisfy `IsSquareIntegrableInducedForm` for `K₁`. The proof shows that `φ_v` satisfies
it for `K₁`, and then applies
`StandardParabolicFamily.isSquareIntegrableInducedForm_of_compact_change` (module
`AdelicSquareIntegrableCompactChange`) to pass to `K₂` with the same `rho`, `hsmooth`, `hcalc`.
The three conditions for `K₁`:

- **Automorphy.** `IsAutomorphicFunctionOn.indicator_finite`, as in the proof of
  `IsAutomorphicFunctionOn.exists_parameterTwist_of_infinite_eq`. By
  `IsIwasawaCompact.height_sub_pair_eq_of_infinite_eq`, `Δ(g)` depends only on the finite
  coordinate of `g`, so `{Δ = v}` is the preimage of a clopen set `T` of finite adeles. `T` is
  stable under left multiplication by `Γ` (left invariance of `Δ`) and under right
  multiplication by the open subgroup `L = K₁,f ∩ K₂,f` (`IsMaximalCompactSubgroup.isOpen_finite`,
  `IsMaximalCompactSubgroup.eq_comap_prod` and `IsIwasawaCompact.height_mul_right`).
- **The `A^n_P` condition** `IsSplitComponentEquivariant`: for `a` in the canonical split centre
  of `M`, `Δ(ι(l a) g) = Δ(g)`, so the indicator takes the same value at `ι(l a) g` and at `g`,
  and the condition for `φ` gives the one for `φ_v`.
- **The `L²` condition.** The integrand for `φ_v` on `K₁ × [M]` is the integrand for `φ`
  multiplied by the indicator of the measurable set `{(k, m) | Δ(k) = v}`, because
  `Δ(ι(l m) k) = Δ(k)`. `Integrable.indicator` gives integrability.

## Assertion 4: the Levi pairings

### The constant

The constant `c > 0` is the one given by `exists_pairing_lintegral_comparison` for `𝓕`, `J`,
`K₁`, `K₂`, before `φ`, `ψ`, `v`, `x`, `x'` are chosen. It comes from
`CompactFactorization.exists_lintegral_compact_eq_of_modular` (module
`Langlands.Analysis.Local.CompactFactorizationModularComparison`), applied to the closed
embedding `ι` (`isClosedEmbedding_map`), the two compacts and their Haar probabilities
`compactHaarProbability`.

### The comparison for nonnegative functions

`exists_pairing_lintegral_comparison` states: for every continuous `θ : G(𝔸) → [0, ∞]` that is
left `Γ`-invariant and vanishes off `{Δ = v}`, and all `x, x' ∈ 𝔄_P` with
`H_P(x') = H_P(x) - v`,

`δ_P(x') ∫_{K₁ × [M]^1} θ(x m k) = c δ_P(x) ∫_{K₂ × [M]^1} θ(x' m k)`

(lower Lebesgue integrals for the pairing measures, `m = Quotient.out z`). The proof:

1. **The slice.** `leviSlice θ g = ∫_{[M]^1} θ(ι_M(m) g) dm`. The integrand
   `(g, z) ↦ θ(ι_M(Quotient.out z) g)` is continuous (`LeftCosetSpace.continuous_out_of_invariant`,
   since `θ` is left invariant under `ι_M(M(F))`), so the slice is measurable.
2. **Tonelli** (`lintegral_pairing_eq_slice`). For `x ∈ 𝔄_P`, `x` commutes with `ι_M(M(𝔸))`
   (`commute_positiveSplitComponent_levi`), and `lintegral_prod` gives
   `∫_{K × [M]^1} θ(x m k) = ∫_K S_θ(x k) dk`, with `S_θ` the slice.
3. **Invariance of the slice under `P(𝔸)^1`** (`leviSlice_normOne_mul`). Let `y ∈ P(𝔸)` with
   `characterLog y = 0`. The Levi decomposition (`leviComponent`, `radicalComponent`, with
   `parabolicRadical_isIso_subgroupMultiplication`) writes `y = l(m) u`. The characters of `U`
   are trivial (`characterLog_eq_zero_of_isUnipotent`) and restriction `X^*(P) → X^*(M)` is
   surjective (`characterRestrict_bijective` of the Levi), so `m ∈ M(𝔸)^1`
   (`exists_levi_normOne_decomposition`). For `n ∈ M(𝔸)^1`, `ι_M(n) ι(y) = ι(u') ι_M(n m)` with
   `u'` in the unipotent radical (normality of the radical), `θ` is left invariant under
   `ι(u')`, and `z ↦ z m` preserves the quotient measure
   (`measurePreserving_rightTranslate_normOneRationalQuotientHaarMeasure`, with the right
   invariance of Haar measure on `M(𝔸)^1` from `normOneHaarRightInvariant` for the connected
   reductive Levi). Hence `S_θ(ι(y) g) = S_θ(g)`.
4. **The equivariant extension.** `exists_characterLog_section` gives a continuous homomorphism
   `σ : 𝔞_P → P(𝔸)` with `characterLog ∘ σ = id`: the `PositiveRealTorus.logSection` of the
   split component, set up as in `standardPositiveLog`. Put `a(g) = σ(H_P^{K₁}(g))`, a continuous
   function of `g` (`IsIwasawaCompact.continuous_height`), and

   `Φ(g) = δ_P(a(g)) S_θ(ι(x a(g)⁻¹) g)`.

   `Φ` is measurable. For `q ∈ P(𝔸)`, `a(ι(q) g) = σ(H_P(q)) a(g)`, the element
   `x a(ι(q) g)⁻¹ q a(g) x⁻¹` has zero logarithm, and `δ_P` depends only on the logarithm
   (`characterNorm_eq_of_characterLog_eq`). With step 3 this gives
   `Φ(ι(q) g) = δ_P(q) Φ(g)`. The modular character of `P(𝔸)` is `δ_P`
   (`modularCharacter_eq_characterNorm_of_local` with
   `PlaceGroupPoints.localModularCharacterAdjointDeterminant`, `P` smooth), so
   `exists_lintegral_compact_eq_of_modular` gives `∫_{K₁} Φ = c ∫_{K₂} Φ`.
5. **Evaluation on the compacts.** For `k ∈ K₁`, `H_P^{K₁}(k) = 0`, so `a(k) = 1` and
   `Φ(k) = S_θ(x k)`. For `k ∈ K₂`, `H_P^{K₂}(k) = 0`, so `H_P^{K₁}(k) = Δ(k)`. If `Δ(k) = v`,
   `a(k) = σ(v)`, and `x σ(v)⁻¹ x'⁻¹` has zero logarithm, so by step 3
   `Φ(k) = δ_P(σ(v)) S_θ(x' k)`. If `Δ(k) ≠ v`, then `Δ(ι_M(n) ι(w) k) = Δ(k) ≠ v` for all `n`,
   `w`, so both `S_θ(x a(k)⁻¹ k)` and `S_θ(x' k)` vanish. Hence
   `∫_{K₁} S_θ(x k) dk = c δ_P(σ(v)) ∫_{K₂} S_θ(x' k) dk`. Since
   `characterLog x = characterLog (x' σ(v))`, `δ_P(x) = δ_P(x') δ_P(σ(v))`; multiplying by
   `δ_P(x')` and applying step 2 gives the displayed identity.

The proof does not need `x σ(v)⁻¹ = x'` in `𝔄_P`; the `P(𝔸)^1`-invariance of the slice
replaces it.

### From nonnegative to complex integrands

Let `Θ = φ_v · conj ψ`. It is continuous (the fibre is clopen,
`IsClopen.continuous_indicator`), left `Γ`-invariant, and zero off `{Δ = v}`. The two pairing
integrands are `z ↦ Θ(x m k)` on `K₁ × [M]^1` and `z ↦ Θ(x' m k)` on `K₂ × [M]^1`; both are
continuous (`continuous_pairing_integrand`), hence strongly measurable.

- **Integrability.** The comparison for `θ = ‖Θ‖ₑ` relates the two lower integrals by positive
  finite factors (`δ_P(x')`, `c δ_P(x)`), so one is finite exactly when the other is; with
  `hasFiniteIntegral_iff_enorm` this is the equivalence of integrability.
- **The integral identity.** If both are integrable, apply the comparison to
  `θ = ofReal(± Re Θ)` and `ofReal(± Im Θ)` and use
  `integral_eq_lintegral_pos_part_sub_lintegral_neg_part`: for the real and imaginary parts,
  `δ_P(x') ∫ = c δ_P(x) ∫`. With `integral_re`, `integral_im` this holds for the complex
  integrals, and dividing by `δ_P(x) δ_P(x')` gives
  `δinv x * ∫_{K₁} = c * (δinv x' * ∫_{K₂})`. If neither is integrable, both Bochner
  integrals are `0`.

## Relation to the route in the statement's Markdown

The statement's Markdown sketches the measure comparison (★) through regular measures on the
compact quotient `P(𝔸) \ G(𝔸)` and lower semicontinuous `δ`-equivariant functions. The Lean
proof replaces that step by `exists_lintegral_compact_eq_of_modular`, which holds for every
measurable `δ`-equivariant function and is proved from the factorization of Haar measure on
`G(𝔸) = P(𝔸) K` (`CompactFactorization.exists_pos_eq_smul_map_mul_prod`), without a measure on
the quotient. It also uses the modular character of `P(𝔸)` and a left Haar measure of `P(𝔸)`
instead of the Iwasawa-compatible Levi measures; the constant is the ratio of the two
factorization constants. The equivariant function `Φ` is the function `f̃` of that Markdown.

## Sources

P. Delorme, *On the spectral theorem of Langlands* (2023), (3.7), p. 15, registered as
`delorme-2023-spectral-theorem-langlands` (the pairing). C. Mœglin and J.-L. Waldspurger,
*Spectral Decomposition and Eisenstein Series* (1995), I.1.13, printed p. 18, registered as
`moeglin-waldspurger-1995-spectral-decomposition` (the measures). E. Lapid (2011), §2, p. 311,
registered as `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (`A^2_P`). The
comparison itself is derived; the sources fix one compact.
