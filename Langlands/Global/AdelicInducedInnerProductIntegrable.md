# Integrability of the integrand of the inner product on `A^2_P`

Module `Langlands.Global.AdelicInducedInnerProductIntegrable`.

## Result

For a parabolic `P = MU` with a Levi retraction `π` (`l ≫ π = 𝟙 M`), a connected reductive
Levi `M`, a split component `a : A_M → M` with `A_M` a split torus, a compact subgroup `K`
of `G(𝔸)`, any Haar measure `μ_M` on `M(𝔸)`, coordinates `e : ℝⁿ ≃ₗ[ℝ] X^*(P) ⊗ ℝ`, and a
continuous compactly supported weight `β : ℝⁿ → ℝ`, the theorem
`InducedInnerProductIntegrable.integrable_inducedInnerProduct_integrand` proves the
following. For all `φ, ψ` with `IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l`,
the function

`(k, x) ↦ β(y(x.out)) · δ_P(x.out)⁻¹ · φ(p(l x.out) k) · conj ψ(p(l x.out) k)`

on `K × RationalQuotient F M` is `Integrable` for
`(compactHaarProbability F G K hKc).prod (discreteQuotientMeasure (rationalSubgroup F M) _ μM)`.
Here `y(m) = parameterCoordinates F P e (characterLog F P (l m))` and
`δ_P(m)⁻¹ = parameterPower F P (-modulusParameter F P) (l m)`. This is exactly the integrand
and measure of `inducedInnerProduct` (`Langlands/Global/AdelicInducedInnerProduct.lean`).
The theorem does not use the Iwasawa factorization of `K`, maximality of `K`, the
compatibility of `μ_M`, reductivity of `G` or `∫ β = 1`.

The module `Langlands.Global.AdelicInducedInnerProductIntegrableProof` specializes this
theorem to `InducedInnerProductIntegrableStatement`.

## Provenance

Internal infrastructure for the proof of the published `WavePacketIsometryStatement` (Lapid
2011, Theorem 2; Arthur 2005, Theorem 7.2(b)). Lapid 2011, §2 (printed p.311), defines `A^2_P`
by the finiteness of `‖φ‖²_P = ∫_{A_M U(𝔸) M(F) \ G(𝔸)} |φ|²` and uses the inner product of
this Hilbert norm. He takes its absolute convergence for granted. The proof below follows the
standard argument: Cauchy–Schwarz, the factorization `M(𝔸) = A_M × M(𝔸)^1`, and the
`A_M`-equivariance of forms in `A^n_P`. No new source claim is made.

## Proof

**Generic quotient lemmas** (namespace `LeftCosetSpace`). For a subgroup `Γ` of a group `H`:
`exists_out_mk` (a representative differs from the point by a left factor in `Γ`),
`out_mk_of_invariant`, and `invariant_sup` (invariance under `Γ` and `Δ` gives invariance under
`Γ ⊔ Δ`). Next, `continuous_out_of_invariant`: if `f : X × H → E` is continuous and left
`Γ`-invariant in the second variable, then `(x, q) ↦ f(x, q.out)` is continuous on
`X × Γ \ H`. The proof uses that `id × mk` is an open quotient map. `measurable_out_of_invariant`
is the measurable analogue for the quotient sigma algebra. `lintegral_discreteQuotientMeasure`:
the lower integral of `q ↦ f(q.out)` for `discreteQuotientMeasure Γ hΓ ν` is
`∫⁻_{fundamentalDomain Γ hΓ} f dν` for measurable invariant `f`.

**Algebra.** `characterLog_map_of_mem_normOne`: for `x` in `M(𝔸)^1`,
`characterLog F P (l x) = 0`. Consequently `characterLog F P (l (x m))`,
`characterLog F P (l (m x))` and every `parameterPower F P λ` of these points are unchanged by
such `x` (`characterLog_map_mul_left/right`, `parameterPower_map_mul_left/right`,
`parameterPower_map_of_mem_normOne`). The next lemmas are `parameterPower_mul`,
`parameterPower_add` and `parameterPower_zero`. Then `neg_modulus_add_half_add_half`:
`-2ρ_P + ρ_P + ρ_P = 0`. It gives `enorm_modulus_mul_half_sq`, `|m^{-2ρ_P}| · |m^{ρ_P}|² = 1`.
Continuity of the real and complex parameter pairings (by induction on tensors) gives
continuity of `parameterPower F P λ` and of `parameterCoordinates F P e`.
`parameterCoordinates_injective` uses the basis `e(Pi.basisFun)`. `realCharacterDualMap_injective`:
restriction along `l` is injective on real duals when `l ≫ π = 𝟙 M`.

**Forms.** `form_rational_mul`: for `x ∈ M(F)`, `χ(p(l(x m)) g) = χ(p(l m) g)`, because
`p(l x)` lies in `parabolicQuotientSubgroup`. `form_canonical_mul` is the `A^n_P` condition
`χ(p(l(a m)) g) = (l a)^{ρ_P} χ(p(l m) g)` for `a` in the canonical split-centre subgroup.

**The split component.** For `b` in the positive points `intrinsicSubgroup F A` of `A_M`,
`positiveCoordinates a e l b = y(positivePointMap b)` (the selected definition of this
record). It is additive (`positiveCoordinates_mul`) and continuous. It is injective
(`positiveCoordinates_injective`): `parameterCoordinates` is injective, `realCharacterDualMap l`
is injective, and `positiveFactor` recovers `b` from `characterLog F M (positivePointMap b)`
(`positivePointMap_injective_of_characterLog`). This step requires injectivity of
`characterRestrict a` and a splitting `eA` of `A`. Composed with the inverse of
`positiveLogCoordinateEquiv` it is a continuous additive, hence real-linear, injective map
`ℝ^I → ℝⁿ`, which is a closed embedding. So `b ↦ β(positiveCoordinates a e l b)` has compact
support (`hasCompactSupport_positiveCoordinates`).

**Decomposition.** `isFundamentalDomain_positiveSlice`: for central `a`, the set
`{n ∈ M(𝔸)^1 | positivePointMap b · n ∈ s}` is a fundamental domain of `M(F)` in `M(𝔸)^1`,
where `s` is the chosen fundamental domain of `M(F)` in `M(𝔸)`.
`setLIntegral_fundamentalDomain_eq` uses `μ_M = c · haar`, the measure-preserving
decomposition `M(𝔸) = A_M^+ × M(𝔸)^1` (`map_normalizedPositiveHaarMeasure_prod`) and Tonelli.
For measurable `H` with `H(positivePointMap b · n) = B(b) g(n)` and `g` invariant under
`M(F)`, it shows

`∫⁻_s H dμ_M = c · (∫⁻ B dν⁺) · ∫⁻_{s₁} g d haar`,

where `s₁` is the chosen fundamental domain of `M(F)` in `M(𝔸)^1`.
`lintegral_canonicalMeasure`: for measurable `H` invariant under the canonical
`A_M M(F)`, `∫⁻_{[M]} H(q.out) d canonicalMeasure = ∫⁻_{s₁} H d haar`, by unfolding
`canonicalMeasure` as the pushforward of the norm-one quotient measure.

**Main.** `integrable_weightedSquare`: for `χ ∈ A^2_P`, the weighted square
`W(k, m) = β(y m) δ_P(m)⁻¹ χ(p(l m) k)²` is integrable on `K × M(F) \ M(𝔸)`. The data `I`,
`eA`, injectivity and finite index of `characterRestrict a` come from `IsSplitTorus A` and the
Library theorem `characterRestriction`, applied to the connected reductive `M` and the split
component `a`. Centrality of `a` is part of `IsSplitComponent`. `W` is continuous and
`M(F)`-invariant in `m`, so `(k, q) ↦ W(k, q.out)` is continuous. By Tonelli and
`lintegral_discreteQuotientMeasure`, `∫⁻ |W|` is `∫⁻_K ∫⁻_s |W(k, m)| dμ_M(m) dk`. Write
`m = positivePointMap b · n`. The norm-one factor does not change `y` or `δ_P`, and
`form_canonical_mul` with `enorm_modulus_mul_half_sq` gives
`|W(k, positivePointMap b · n)| = |β(positiveCoordinates b)| · |χ(p(l n) k)|²`. So
`setLIntegral_fundamentalDomain_eq` gives
`c · (∫⁻ |β ∘ positiveCoordinates| dν⁺) · ∫⁻_K ∫⁻_{s₁} |χ(p(l n) k)|²`.
The first integral is finite by compact support and continuity. With
`lintegral_canonicalMeasure` (on `M(𝔸)^1`, `δ_P = 1`) and Tonelli on `K × [M]`, the last factor
equals `∫⁻_{K × [M]} |δ_P(x.out)⁻¹| |χ(p(l x.out) k)|²`. That integral is finite by
`IsSquareIntegrableInducedForm`.

`integrable_inducedInnerProduct_integrand`: the integrand is continuous on
`K × M(F) \ M(𝔸)` (same invariance argument). Its norm `X ab` with `X = |β(y)| |δ_P⁻¹|`,
`a = |φ(·)|`, `b = |ψ(·)|` is at most `X a² + X b²` (`mul_le_add_sq_aux`), the sum of the
norms of the two integrable weighted squares. `Integrable.mono'` concludes.
