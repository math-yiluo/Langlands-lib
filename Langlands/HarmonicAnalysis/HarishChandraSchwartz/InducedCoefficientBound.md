# Coefficients of induced representations are bounded by `Ξ` (Waldspurger, Lemma VI.2.2)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientBound`,
namespace `Langlands.HarishChandraSchwartz`. It imports the published
`LeviWeightIntegrability` (for `leviXiWeight`), which imports `SphericalLevi` (for
`LeviData`, `leviComponent`, `LeviData.xi_eq_integral`) and `Spherical` (for `xi`, `xi_pos`,
`normalizedHaar`, `IsIwasawaPair`). From Mathlib it uses `norm_integral_le_of_norm_le` and
`Integrable.of_integral_ne_zero`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

Lemma VI.2.2, printed p. 298 (PDF p. 64): for `ψ ∈ C^∞(O, P)` there is `C > 0` such that
`|(E_P^G ψ_ω)(g)| ≤ C Ξ(g)` for all `ω ∈ O` and `g ∈ G`. Proof, printed pp. 298–299 (PDF
pp. 64–65): one reduces to `|⟨I_P^G(ω ⊗ χ)(g) v, v̌⟩| ≤ C Ξ(g)` uniformly in `χ ∈ Im X(M)`; with
`v_χ` the element of `I_P^G E_χ` restricting to `v` on `K`,
`⟨I_P^G(ω ⊗ χ)(g) v, v̌⟩ = ∫_K ⟨v_χ(kg), v̌(k)⟩ dk
= ∫_K χ δ_P^{1/2}(m_P(kg)) ⟨ω(m_P(kg)) v(k_P(kg)), v̌(k)⟩ dk`; by Corollary III.1.2,
`|⟨ω(m_P(kg)) v(k_P(kg)), v̌(k)⟩| ≤ C Ξ^M(m_P(kg))` uniformly; hence the coefficient is at most
`C ∫_K δ_P^{1/2}(m_P(kg)) Ξ^M(m_P(kg)) dk`, "et il reste à appliquer le Lemme II.1.6".

This module proves the last two steps: from the pointwise bound on the integrand to the bound by
`C Ξ(g)` through Lemma II.1.6. The representation of the induced coefficient as a `K`-integral,
the bound of the integrand by Corollary III.1.2, the reduction from `E_P^G ψ_ω` to such
coefficients and the uniformity over the orbit `O` are not formalized here.

## Scope: abstract data and explicit hypotheses

The data are those of `SphericalLevi`: a topological group `G` with Borel structure, subgroups
`K` (compact, open), `P₀ ⊆ P` and `M ⊆ P`, characters `δ₀`, `δ_P`, `δ₀^M`, a Levi projection
`m_P : P →* M`, and `hL : LeviData K P₀ P M δ₀ δP δ₀M mP`. The hypotheses of
`LeviData.norm_compactIntegral_le_xi`:

- `[SecondCountableTopology G]`, `[CompactSpace K]`, `[CompactSpace (K.subgroupOf M)]`;
- `hK : IsOpen (K : Set G)`, `hP₀K : IsIwasawaPair P₀ K` (`G = P₀ K`),
  `hM : IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M)` (`M = (P₀ ∩ M)(K ∩ M)`),
  `hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1`;
- `Φ : K → G → ℂ` and `C : ℝ` with
  `hΦ : ∀ k x, ‖Φ k x‖ ≤ C * leviXiWeight (hP₀K.mono hL.le_P₀) mP δP hM δ₀M x`, i.e.
  `|Φ(k, x)| ≤ C δ_P(m_P(x))^{1/2} Ξ^M(m_P(x))`.

`LeviData.norm_compactIntegral_le_xi_uniform` has the same hypotheses for a family
`Φ : ι → K → G → ℂ` with one constant `C`.

## Definitions

- `compactIntegral K Φ g = ∫_K Φ(k, k g) d(normalizedHaar K)(k)`. With
  `Φ(k, x) = ⟨v_χ(x), v̌(k)⟩` this is Waldspurger's `⟨I_P^G(ω ⊗ χ)(g) v, v̌⟩`; its comparison with
  a Library coefficient map is not made here.

## Results

- `LeviData.norm_compactIntegral_le_xi` (**Lemma VI.2.2, analytic core**):
  `‖compactIntegral K Φ g‖ ≤ C Ξ(g)` for every `g`, with `Ξ = xi hP₀K δ₀`.
- `LeviData.norm_compactIntegral_le_xi_uniform`: the same bound with one constant for a family.

## Proof notes

By `LeviData.xi_eq_integral` (Lemma II.1.6),
`Ξ(g) = ∫_K δ_P(m_P(kg))^{1/2} Ξ^M(m_P(kg)) dk`. Since `Ξ(g) > 0` (`xi_pos`), this integrand is
integrable (`Integrable.of_integral_ne_zero`). Then
`‖∫_K Φ(k, kg) dk‖ ≤ ∫_K C δ_P(m_P(kg))^{1/2} Ξ^M(m_P(kg)) dk = C Ξ(g)`
(`norm_integral_le_of_norm_le`); no integrability of `Φ` is needed.

## Relation to the Library

- `LeviWeightIntegrability` defines `leviXiWeight` (used for Lemma II.4.3); it is reused here.
- `Langlands.Plancherel.productInducedCoefficientMap_integral` (Worker 200) writes the induced
  coefficient as an integral of `productInducedCoefficientIntegrand` against the Bruhat measure
  `normalizedInductionBruhatMeasure` on the whole group, not against normalized Haar measure on
  `K`; the comparison of that representation with `compactIntegral` is open and is not asserted.

## Open obligations

The `K`-integral representation of the actual induced coefficients (with `G = P K` and the
normalization of the measures), the uniform bound of the integrand from Corollary III.1.2 on `M`,
and the reduction of `E_P^G ψ_ω` to such coefficients are not proved here.
