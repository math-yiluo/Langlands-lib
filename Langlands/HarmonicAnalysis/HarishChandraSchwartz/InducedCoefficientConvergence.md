# Absolute convergence in the proof of Waldspurger's Lemma VII.1.2

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientConvergence`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientXi`:
  `inducedIntegrandKernel`, `inducedIntegrandKernel_mul` and `norm_inducedIntegrandKernel_le`
  (the pointwise bound in the proof of Lemma VI.2.2). Through its imports it also supplies
  Worker 200's `productInducedCoefficientObject` (`L(ω, P)`), `CompactInduction.integrand`,
  `CompactInduction.measure` with `CompactInduction.measure_eq_normalizedHaar`,
  `Induction.eval_isLocallyConstant`, the spherical function `xi` with `xi_pos` and
  `continuous_xi`, `iwasawaWeight_nonneg`, `normalizedHaar`, `leviXiWeight`, `LeviData` with
  `LeviData.xi_eq_integral` (Lemma II.1.6), `IsIwasawaPair` and `IsUnimodularModulus`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedPairing`: `Space.integrable_mul`
  (`f φ` is integrable for `f ∈ C(G)` and continuous `φ` with `ν_{-r}(φ) < ∞`), and through its
  imports `Space`, `nu`, `weight` and `L2Weights`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`).

- Proof of Lemma VII.1.2, printed p. 315 (PDF p. 81): for `v ∈ I_P^G E`, `v̌ ∈ I_P^G Ě` and
  `f ∈ C(G)`, `(v ⊗ v̌, f̂(ω, P)) = ∫_G ∫_{P\G} conj(⟨v(hg), v̌(h)⟩) f(g) dh dg` (the overbar,
  checked on the page image, is written `conj`), and "Il résulte de la preuve du Lemme VI.2.2 et
  du Lemme II.1.5 que cette dernière intégrale est absolument convergente."
- Lemma VI.2.2 and its proof, printed pp. 298–299 (PDF pp. 64–65): for `ψ ∈ C^∞(O, P)` there is
  `C > 0` with `|(E_P^G ψ_ω)(g)| ≤ C Ξ(g)` for all `ω ∈ O` and `g ∈ G`. The proof writes
  `⟨I_P^G(ω ⊗ χ)(g) v, v̌⟩ = ∫_K ⟨v_χ(kg), v̌(k)⟩ dk` and, by Corollary III.1.2, bounds the
  integrand by `C δ_P^{1/2}(m_P(kg)) Ξ^M(m_P(kg))` for all `g ∈ G` and `k ∈ K`; "il reste à
  appliquer le Lemme II.1.6".
- Lemma II.1.5, printed p. 252 (PDF p. 18): "Il existe `d ∈ ℕ` tel que l'intégrale
  `∫_G Ξ(g)² (1 + σ(g))^{-d} dg` soit convergente."
- Lemma II.1.6, printed p. 252 (PDF p. 18): "Pour tout `g ∈ G`, on a l'égalité
  `Ξ(g) = ∫_K δ_P(m_P(kg))^{1/2} Ξ^M(m_P(kg)) dk`."

The integrand and the convergence statement are source content (the double integral and its
absolute convergence). The Lean proof follows the route the source indicates. The integral over
`P\G` is the integral over `K` with its Haar probability, as in Worker 200's
`CompactInduction.coefficientMap`. `nu_zero_ofReal_le_one`, `continuous_integrand_uncurry` and
`lintegral_leviXiWeight_mul` are derived.

### Correspondence with the source

- `L(ω, P) = I_{P×P}^{G×G}(E ⊗ Ě)` is `productInducedCoefficientObject h hU A`. For
  `ψ = v ⊗ v̌`, `CompactInduction.integrand h hU A K g ψ k` is `⟨v(k g), v̌(k)⟩`; for general `ψ`
  it is the pairing `E ⊗ Ě → ℂ` applied to `ψ(k g, k)`.
- `coefficientPairingIntegrand h hU A K ψ f (g, k)` is `conj⟨ψ(k g, k)⟩ f(g)`, the integrand of
  `∫_G ∫_{P\G} conj(⟨v(hg), v̌(h)⟩) f(g) dh dg` with `h = k ∈ K`.
- `Ξ` is the spherical function `xi hP₀K δ₀` of the Iwasawa data `(P₀, K, δ₀)`, and `Ξ^M` is
  `xi hMK δ₀M` for `(P₀ ∩ M, K ∩ M, δ₀^M)`. `C(G)` is `Space (xi hP₀K δ₀) σ`. The hypothesis
  `hw : L2Weights μ (xi hP₀K δ₀) σ` contains Lemma II.1.5 (`∫_G Ξ² (1 + σ)^{-d} dμ < ∞` for some
  `d`) together with positivity of `Ξ` and nonnegativity of `σ`.
- `δ_P` on `M` is `HaarModulus.closedRestrictCharacter U hU M …`, and `m_P` is `h.projection`.
  `leviXiWeight … x` is `δ_P(m_P(x))^{1/2} Ξ^M(m_P(x))` for the Levi component of the
  factorization `x = p k`.

## Scope and hypotheses

### Weight section

`nu_zero_ofReal_le_one` takes a type `X`, `Ξ σ : X → ℝ` and `hΞ : ∀ g, 0 < Ξ g`.

### Convergence section

`G` is a locally compact, nonarchimedean, second countable, Hausdorff topological group with
`MeasurableSpace` and `BorelSpace`. `P`, `M`, `U` are subgroups with
`h : IsSemidirectDecomposition P M U` and `hU : IsClosed U`; `A : SmoothRep ℂ M`;
`K : OpenSubgroup G` with `hK : IsCompact K`; a subgroup `P₀` with characters
`δ₀ : P₀ →* ℝ≥0ˣ` and `δ₀M : P₀ ∩ M →* ℝ≥0ˣ`; and instances `[CompactSpace K]`,
`[CompactSpace (K ∩ M)]`.

- `continuous_integrand_uncurry` and `coefficientPairingIntegrand` use only `h`, `hU`, `A`, `K`
  and the instances `Group`, `TopologicalSpace`, `LocallyCompactSpace`, `NonarchimedeanGroup` on
  `G`.
- `lintegral_leviXiWeight_mul` takes `h`, `hU`, `K`, `hK`, the instances on `G` except
  `T2Space`, `[CompactSpace K]`, `[CompactSpace (K ∩ M)]`, and:
  `hL : LeviData K P₀ P M δ₀ δ_P δ₀M h.projection` (with
  `δ_P = closedRestrictCharacter U hU M …`), `hP₀K : IsIwasawaPair P₀ K` (`G = P₀ K`),
  `hMK : IsIwasawaPair (P₀ ∩ M) (K ∩ M)`, `hδ₀ : ∀ p : P₀, p ∈ K → δ₀ p = 1`, and a constant
  `C > 0`.
- `integrable_coefficientPairingIntegrand` takes `[Nonempty (CompactOpenSubgroup G)]`, `hK`,
  `hδ : IsUnimodularModulus U hU` (`U` unimodular), `hL`, `hP₀K`, `hMK`, `hδ₀`, and
  `hcoeff` (Corollary III.1.2 for `M`): for all `v ∈ A` and smooth dual vectors `ℓ` there is
  `C > 0` with `‖ℓ(A(m) v)‖ ≤ C Ξ^M(m)` for all `m ∈ M`. It also takes an s-finite measure `μ`
  on `G`, `σ : G → ℝ` with `hw : L2Weights μ (xi hP₀K δ₀) σ`, `ψ ∈ L(ω, P)` and
  `f ∈ Space (xi hP₀K δ₀) σ`. These are the hypotheses of the Library's
  `norm_inducedIntegrandKernel_le` and `LeviData.xi_eq_integral`, plus `hw`; no admissibility,
  square integrability or modulus hypothesis on `P` is needed. `T2Space G` is not used.

## Definitions

- `coefficientPairingIntegrand h hU A K ψ f : G × K → ℂ`, for `f : G → ℂ`, is
  `(g, k) ↦ conj(CompactInduction.integrand h hU A K g ψ k) * f g`.

## Results

- `nu_zero_ofReal_le_one`: `ν_0(Ξ) ≤ 1` for the weight `Ξ` itself, viewed as a complex
  function (`ν_r(φ) = sup_g |φ(g)| Ξ(g)⁻¹ (1 + σ(g))^r`).
- `continuous_integrand_uncurry`: `(g, k) ↦ CompactInduction.integrand h hU A K g ψ k` is
  continuous on `G × K`.
- `lintegral_leviXiWeight_mul`: for `C > 0`,
  `∫⁻_K ofReal(C δ_P(m_P(k g))^{1/2} Ξ^M(m_P(k g))) dk = ofReal(C Ξ(g))` for the Haar probability
  `CompactInduction.measure K hK`. This is Lemma II.1.6 multiplied by `C`, as a lower integral.
- `integrable_coefficientPairingIntegrand`: `coefficientPairingIntegrand h hU A K ψ f` is
  integrable on `G × K` for `μ × CompactInduction.measure K hK`. This is the absolute
  convergence asserted in the proof of Lemma VII.1.2, and it is the hypothesis `hint` of
  `inducedFourierTransform_eq_constantTermInducedFourierTransform` (staged module
  `InducedConstantTermFourier`) for `Ξ = xi hP₀K δ₀`.

## Proof notes

1. `nu_zero_ofReal_le_one`: each term of the supremum is `ofReal(Ξ g) ofReal(Ξ(g)⁻¹) = 1`.
2. `continuous_integrand_uncurry`: the integrand is the pairing `E ⊗ Ě → ℂ` composed with the
   locally constant evaluation of `ψ` (`Induction.eval_isLocallyConstant`) at
   `(g, k) ↦ (k g, k)`, which is continuous.
3. `lintegral_leviXiWeight_mul`: rewrite `CompactInduction.measure K hK` as the Haar probability
   `normalizedHaar K`. The function `k ↦ δ_P(m_P(k g))^{1/2} Ξ^M(m_P(k g))` is integrable because
   its integral is `Ξ(g) > 0` (`LeviData.xi_eq_integral`, `xi_pos`), and it is nonnegative. So
   the lower integral of `ofReal(C ·)` is `ofReal` of the integral, which is `C Ξ(g)`.
4. `integrable_coefficientPairingIntegrand`: measurability follows from continuity (step 2 and
   continuity of `f`). For the finite integral, write
   `CompactInduction.integrand h hU A K g ψ k = inducedIntegrandKernel ψ k (k g)` and use
   `norm_inducedIntegrandKernel_le`: `|⟨ψ(k g, k)⟩| ≤ C δ_P(m_P(k g))^{1/2} Ξ^M(m_P(k g))`. By
   Tonelli (`lintegral_prod_le`) and step 3, the lower integral over `G × K` is at most
   `C ∫_G Ξ(g) |f(g)| dμ(g)`. That integral is finite by `Space.integrable_mul` with
   `φ = Ξ` and `r = 0` (step 1), which uses `hw` (Lemma II.1.5).

## Relation to the Library

- `InducedCoefficientXi` proves Lemma VI.2.2 for one coefficient, `|E_P^G ψ(g)| ≤ c Ξ(g)`. This
  module integrates the same pointwise bound before integrating over `K`, which gives the absolute
  convergence of the double integral.
- The staged module `InducedConstantTermFourier` (Lemma VII.1.2) takes this convergence as its
  hypothesis `hint`. Combining the two for `Ξ = xi` is left to a later module.

## Open obligations

- Instantiating `hw` (Lemma II.1.5 for Waldspurger's `Ξ` and `σ`), `hcoeff` (Corollary III.1.2
  for `M`) and the Iwasawa data (`hL`, `hP₀K`, `hMK`, `hδ₀`) for a reductive group is not done
  here.
