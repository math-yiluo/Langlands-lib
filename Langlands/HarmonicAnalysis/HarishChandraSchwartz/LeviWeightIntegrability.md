# Lemma II.4.3 from Lemma II.4.2

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.LeviWeightIntegrability`,
namespace `Langlands.HarishChandraSchwartz`. It imports the published modules
`ConstantTermBound` (`UnipotentWeightIntegrable`, `IsConjModulus.lintegral_comp`; through
`ConstantTermInd`, `IsConjModulus` and `conjUnipotent`) and `SphericalLevi` (`LeviData`,
`leviComponent`, `IsIwasawaPair.mono`, `LeviData.iwasawaWeight_mul`), and through them
`Spherical` (`IsIwasawaPair`, `iwasawaFactor`, `iwasawaWeight`, `normalizedHaar`, `xi`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- Lemma II.4.2 (printed p. 261, PDF p. 27): for some `d ∈ ℕ` the integral
  `∫_Ū δ_0(m_0(ū))^{1/2} (1 + σ(ū))^{-d} dū` converges.
- Lemma II.4.3 (printed pp. 261–262, PDF pp. 27–28): for some `d ∈ ℕ` the integral
  `∫_Ū δ_P(m_P(ū))^{1/2} Ξ^M(m_P(ū)) (1 + σ(ū))^{-d} dū` converges. Proof: for
  `k ∈ K ∩ M` change variables `ū ↦ k ū k^{-1}` in the integral of II.4.2 and integrate
  over `k ∈ K ∩ M`; then `m_0(k ū k^{-1}) = m_0(k m_P(ū))`, so
  `δ_0(m_0(k ū k^{-1})) = δ^M_0[m_0(k m_P(ū))] δ_P(m_P(ū))`, and the inner integral
  `∫_{K∩M} δ^M_0[m_0(k m_P(ū))]^{1/2} dk` is `Ξ^M(m_P(ū))`. The remark after
  Proposition II.4.5 (printed p. 263) says that II.4.3 also holds for semi-standard `P`.

## Scope: abstract data and explicit hypotheses

The data are those of `SphericalLevi`: a topological group `G` with its Borel σ-algebra,
subgroups `K`, `P₀`, `P`, `M` with `G = P₀ K` (`hP₀K`), `M = (P₀ ∩ M)(K ∩ M)` (`hM`),
`K ∩ M` compact, characters `δ₀` of `P₀`, `δ_P` of `M`, `δ₀^M` of `P₀ ∩ M`, and a Levi
projection `m_P : P →* M`, related by the Prop structure `LeviData` (`δ₀` trivial on the
kernel of `m_P`, `δ₀ = δ_P δ₀^M` on `P₀ ∩ M`, `δ_P = 1` on `K ∩ M`). Two further
hypotheses are explicit arguments of both results: `K` is open (`hK`), and `δ₀` is
trivial on `P₀ ∩ K` (`hδ₀ : ∀ p : P₀, p ∈ K → δ₀ p = 1`). The second is not part of
`LeviData`, and it is different from the triviality of `δ₀` on the kernel of `m_P`; it is
what makes `φ₀(p k) = δ₀(p)^{1/2}` independent of the factorization `g = p k` and right
`K`-invariant (`iwasawaWeight_mul`, `iwasawaWeight_mul_right` of `Spherical`). For
Waldspurger's `δ₀` it holds because `P₀ ∩ K` is compact. `Ξ^M` is
`xi hM δ₀M`, the spherical function of `M` built by the integral formula of II.1, and the
weight `φ₀(p k) = δ₀(p)^{1/2}` is `iwasawaWeight hP₀K δ₀`. In addition `U` (Waldspurger's
`Ū`) is a second-countable subgroup normalized by `M`, with an s-finite measure `ν`
satisfying `IsConjModulus hMU ν δ` for a character `δ` of `M` trivial on `K ∩ M`, and `σ`
is measurable, nonnegative and invariant under conjugation by `K ∩ M`. For Waldspurger's
data, `ν` is a Haar measure on `Ū` and `IsConjModulus` with `δ = δ_{P̄}` holds by
`isConjModulus_restrictCharacter` of `ConstantTermInd` once the Haar modulus is
identified; that identification and the realization of the other data are not done here.

## Definitions

- `leviXiWeight hPK mP δP hM δ₀M g = δ_P(m_P(g))^{1/2} Ξ^M(m_P(g))`, with
  `m_P(g) = leviComponent hPK mP g`. This is the integrand of Lemma II.1.6 (proved as
  `LeviData.xi_eq_integral` in `SphericalLevi`) and the weight of Lemma II.4.3.

## Results

- `LeviData.iwasawaWeight_conj`: under `LeviData`, `G = P₀ K`, `M = (P₀ ∩ M)(K ∩ M)` and
  `hδ₀`, for `k ∈ K ∩ M` and `u ∈ G`,
  `φ₀(k u k^{-1}) = δ_P(m_P(u))^{1/2} φ₀^M(k m_P(u))`.
- `LeviData.unipotentWeightIntegrable` (Lemma II.4.3): under all the hypotheses of the
  scope paragraph (including `hK` and `hδ₀`), if
  `UnipotentWeightIntegrable ν (φ₀ ∘ val) σ` (Lemma II.4.2, with the weight
  `φ₀(ū) = δ_0(m_0(ū))^{1/2}`), then
  `UnipotentWeightIntegrable ν (leviXiWeight … ∘ val) σ`:
  `∫⁻_U ofReal(δ_P(m_P(u))^{1/2} Ξ^M(m_P(u)) (1 + σ(u))^{-d}) dν(u) < ∞` for some real
  `d` (the same `d` as in the hypothesis).

## Proof notes

The proof is Waldspurger's. For `k ∈ K ∩ M`, `IsConjModulus.lintegral_comp` with
`δ(k) = 1` and the conjugation invariance of `σ` show that replacing `φ₀(u)` by
`φ₀(k u k^{-1})` does not change the integral of II.4.2. Averaging over `k` against the
Haar probability measure of `K ∩ M` and exchanging the integrals (Tonelli; the integrand
is measurable on `(K ∩ M) × U` because `φ₀` is continuous for open `K` and `U` is second
countable) gives `∫_U (∫_{K∩M} φ₀(k u k^{-1}) dk) (1 + σ(u))^{-d} dν(u) < ∞`. For the inner
integral, `φ₀(k u k^{-1}) = φ₀(k u)` by right `K`-invariance; writing `u = p k'` with
`p ∈ P` and `k' ∈ K`, `φ₀(k u) = φ₀(k p) = δ_P(m_P(p))^{1/2} φ₀^M(k m_P(p))` by
`LeviData.iwasawaWeight_mul`; integrating over `k` gives
`δ_P(m_P(u))^{1/2} Ξ^M(m_P(u))` by the definition of `xi` on `M`.

## Open obligations

Lemma II.4.2 itself (a hypothesis here), the realization of the Levi data and of the
Haar measure and modulus on `Ū` for Waldspurger's group, and second countability of `Ū`
are not proved here.
