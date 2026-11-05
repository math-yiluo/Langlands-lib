# Induced coefficients are bounded by `Ξ` (Waldspurger, Lemma VI.2.2)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientXi`,
namespace `Langlands.HarishChandraSchwartz`. It imports `InducedCoefficientBound` (for
`compactIntegral` and `LeviData.norm_compactIntegral_le_xi`), Worker 200's
`Langlands.Representation.Plancherel.CompactProductCoefficientBounds` (for
`CompactInduction.integrand_bound_levi`), which imports `CompactProductInducedCoefficients` (for
`CompactInduction.integrand`, `CompactInduction.coefficientMap`,
`CompactInduction.coefficientMap_integral` and the probability Haar measure
`CompactInduction.measure K hK` on `K`), and
`Langlands.Representation.Plancherel.CompactCoefficientHaarComparison` (for
`CompactInduction.measure_eq_normalizedHaar`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

Lemma VI.2.2, printed p. 298 (PDF p. 64): "Soit `ψ ∈ C^∞(O, P)`. Il existe `C > 0` tel que
pour tout `ω ∈ O` et tout `g ∈ G`, on ait l'inégalité `|(E_P^G ψ_ω)(g)| ⩽ C Ξ(g)`."

Proof, printed pp. 298–299 (PDF pp. 64–65): one reduces to showing, for `(ω, E) ∈ O`,
`v ∈ I_{K∩P}^K E` and `v̌ ∈ I_{K∩P}^K Ě`, that `|⟨I_P^G(ω ⊗ χ)(g) v, v̌⟩| ⩽ C Ξ(g)` for all
`χ ∈ Im X(M)` and `g ∈ G`. With `v_χ` the element of `I_P^G E_χ` restricting to `v` on `K`,
`⟨I_P^G(ω ⊗ χ)(g) v, v̌⟩ = ∫_K ⟨v_χ(kg), v̌(k)⟩ dk
= ∫_K χ δ_P^{1/2}(m_P(kg)) ⟨ω(m_P(kg)) v(k_P(kg)), v̌(k)⟩ dk`.
"Quand `k` et `g` varient, les éléments `v(k_P(kg))` de `E`, resp. `v̌(k)` de `Ě`, restent dans
des sous-espaces de dimension finie. D'après le Corollaire III.1.2, il existe donc `C > 0` tel
que, pour tout `g ∈ G` et tout `k ∈ K`, on ait
`|⟨ω(m_P(kg)) v(k_P(kg)), v̌(k)⟩| ⩽ C Ξ^M(m_P(kg))`."
Then `|⟨I_P^G(ω ⊗ χ)(g) v, v̌⟩| ⩽ C ∫_K δ_P^{1/2}(m_P(kg)) Ξ^M(m_P(kg)) dk`, "et il reste à
appliquer le Lemme II.1.6".

This module proves the displayed coefficient bound for one inducing representation (the
coefficient of `I_P^G(A)` for a single smooth representation `A` of `M`, for instance
`A = ω ⊗ χ` with `χ` fixed). It combines Worker 200's representation of the actual induced
coefficient as a `K`-integral and their integrand bound from a coefficient bound on `M` with the
analytic core `LeviData.norm_compactIntegral_le_xi` (Lemma II.1.6 applied to the integrand
bound). The uniformity in `χ ∈ Im X(M)` and `ω ∈ O`, and the reduction from `E_P^G ψ_ω` to
these coefficients, are not formalized.

## Scope: data and explicit hypotheses

The group and induction data are those of Worker 200's `CompactProductInducedCoefficients`:
a locally compact nonarchimedean group `G` (`[Group G] [TopologicalSpace G]
[LocallyCompactSpace G] [NonarchimedeanGroup G]`), subgroups `P`, `M`, `U` with
`h : IsSemidirectDecomposition P M U` (`P = M ⋉ U`, `m_P = h.projection`),
`hU : IsClosed (U : Set G)`, a smooth complex representation `A : SmoothRep ℂ M`, and a compact
open subgroup `K : OpenSubgroup G` with `hK : IsCompact (K : Set G)`. The coefficient of the
normalized induced representation is `CompactInduction.coefficientMap h hU A K hK … F`, where
`F` ranges over the product-induced coefficient space `productInducedCoefficientObject h hU A`
(the normalized induction to `G × G` of `A ⊠ Ǎ`), the Library form of the vectors `v ⊗ v̌`
and their sums.

The weight data are those of `SphericalLevi`: a subgroup `P₀` with a character
`δ₀ : P₀ →* ℝ≥0ˣ` and a character `δ₀^M : P₀ ∩ M →* ℝ≥0ˣ`; `Ξ = xi hP₀K δ₀` and
`Ξ^M = xi hMK δ₀M`. The character `δ_P` is taken to be the Haar modulus
`HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer` of the conjugation action of
`M` on `U`.

Hypotheses of `norm_coefficientMap_le_xi` (each is an explicit argument or instance):

- instances `[SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]`,
  `[CompactSpace (K : Subgroup G)]`, `[CompactSpace ((K : Subgroup G).subgroupOf M)]`,
  `[LocallyCompactSpace P]`;
- the hypotheses of `CompactInduction.coefficientMap`: `hP : IsClosed (P : Set G)`,
  `hm : Continuous h.projection`, `hPK : ∀ g, ∃ q ∈ P, ∃ k ∈ K, g = q * k` (`G = P K`),
  `hG : ∀ g, Measure.modularCharacter g = 1` (`G` unimodular),
  `hδP : ∀ q : P, Measure.modularCharacter q = closedRestrictCharacter U hU P … q` (the modular
  character of `P` is the modulus of its action on `U`), `hA : A.IsAdmissible`;
- `hδ : IsUnimodularModulus U hU` (`U` unimodular);
- `hL : LeviData K P₀ P M δ₀ δ_P δ₀^M h.projection` (`P₀ ⊆ P`, `M ⊆ P`, `m_P` is the identity on
  `M`, `ker m_P ⊆ P₀`, `δ₀` trivial on `ker m_P`, `δ₀ = δ_P δ₀^M` on `P₀ ∩ M`, `δ_P` trivial on
  `K ∩ M`);
- `hP₀K : IsIwasawaPair P₀ K` (`G = P₀ K`) and
  `hMK : IsIwasawaPair (P₀ ∩ M) (K ∩ M)` (`M = (P₀ ∩ M)(K ∩ M)`);
- `hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1`;
- `hcoeff` (the conclusion of Corollary III.1.2 for `M`, used as in the source proof): for all
  `v ∈ A` and smooth dual vectors `ℓ` there is `C > 0` with
  `‖ℓ(A(m) v)‖ ≤ C Ξ^M(m)` for every `m ∈ M`;

`norm_inducedIntegrandKernel_le` uses the instances, `hK`, `hδ`, `hL`, `hP₀K`, `hMK` and
`hcoeff` (not `hδ₀` or the coefficient-map hypotheses).

## Definitions

- `inducedIntegrandKernel h hU A K F k x = CompactInduction.integrand h hU A K (k⁻¹ x) F k`, the
  function `Φ(k, x)` with `Φ(k, k g) = integrand(g)(F)(k)`; for `F = v ⊗ v̌` this is
  Waldspurger's `⟨v_χ(kg), v̌(k)⟩` read at `x = kg`.

## Results

- `inducedIntegrandKernel_mul`: `Φ(k, k g) = CompactInduction.integrand h hU A K g F k`.
- `norm_inducedIntegrandKernel_le` (integrand bound): there is `C > 0` with
  `‖Φ(k, x)‖ ≤ C δ_P(m_P(x))^{1/2} Ξ^M(m_P(x))` for all `k ∈ K`, `x ∈ G`, in the form
  `C * leviXiWeight (hP₀K.mono hL.le_P₀) h.projection δ_P hMK δ₀M x`, where `m_P(x)` is the
  Levi component of the factorization `x = q k₁` chosen by `iwasawaFactor`.
- `norm_coefficientMap_le_xi` (**Lemma VI.2.2 for one inducing representation**): there is
  `C > 0` with `‖coefficientMap … F g‖ ≤ C Ξ(g)` for every `g ∈ G`.

## Proof notes

`norm_inducedIntegrandKernel_le`: Worker 200's `CompactInduction.integrand_bound_levi`
(applied with `ξ = Ξ^M`, nonnegative since it is an integral of the nonnegative
`iwasawaWeight`) gives `C` with
`‖integrand(g)(F)(k)‖ ≤ δ_P(m_P(q))^{1/2} C Ξ^M(m_P(q))` whenever `k g = q k₁` with `q ∈ P`,
`k₁ ∈ K`. For `x ∈ G`, `exists_iwasawaFactor` writes `x = q k₁` with `q = iwasawaFactor x`;
applying the bound to `g = k⁻¹ x` gives the claim after unfolding `leviXiWeight` and
`leviComponent`.

`norm_coefficientMap_le_xi`: by `CompactInduction.coefficientMap_integral`, the coefficient at
`g` is `∫_K integrand(g)(F)(k) d(measure K hK)(k)`; by
`CompactInduction.measure_eq_normalizedHaar K hK` (the two probability Haar measures on `K`
agree) and `inducedIntegrandKernel_mul`
this is `compactIntegral K Φ g`, and `LeviData.norm_compactIntegral_le_xi` (Lemma II.1.6)
bounds it by `C Ξ(g)`.

## Relation to the Library

- `InducedCoefficientBound` (`LeviData.norm_compactIntegral_le_xi`) is the analytic step used
  here.
- Worker 200's `CompactProductInducedCoefficients` and `CompactProductCoefficientBounds` supply
  the `K`-integral representation and the integrand bound, and `CompactCoefficientHaarComparison`
  identifies `CompactInduction.measure K hK` with `normalizedHaar (K : Subgroup G)`; this module
  only connects their conclusions.

## Open obligations

- `hcoeff` for square-integrable `ω` (Corollary III.1.2 for `M`), the identification of the
  Library data with Waldspurger's `K`, `P₀`, `δ₀`, the uniformity in `χ ∈ Im X(M)` and
  `ω ∈ O`, and the reduction from `E_P^G ψ_ω` to the coefficients.
