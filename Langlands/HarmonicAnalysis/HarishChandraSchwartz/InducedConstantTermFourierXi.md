# Lemma VII.1.2 and Proposition VII.1.3 for the spherical function `Ξ`

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedConstantTermFourierXi`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedConstantTermFourier`:
  `inducedFourierTransform_eq_constantTermInducedFourierTransform` (Lemma VII.1.2 with the
  hypothesis `hint`) and `constantTermInducedFourierTransform`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientConvergence`:
  `integrable_coefficientPairingIntegrand` (the absolute convergence for `Ξ = xi`);
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitSmoothness`:
  `fourierOrbitSmoothSectionLinear` (the map `f ↦ ψ_f[O, P]` into `C^∞(O, P)` with the hypothesis
  `hint` for every `f` and every representative). Through the imports: `xi`, `LeviData`,
  `IsIwasawaPair`, `productInducedSmoothOrbitSections` and the data of those modules.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`).

- Lemma VII.1.2, printed p. 315 (PDF p. 81): "Pour tout `f ∈ C(G)`, on a l'égalité
  `f̂(ω, P) = f̂^{(P),Ind}(ω)`." Its proof: "Il résulte de la preuve du Lemme VI.2.2 et du
  Lemme II.1.5 que cette dernière intégrale est absolument convergente."
- Proposition VII.1.3, printed p. 316 (PDF p. 82): "Pour tout `f ∈ C(G)`, la fonction
  `ψ_f[O, P]` appartient à `C^∞(O, P)`."
- II.1, printed p. 250 (PDF p. 16): the spherical function `Ξ(g) = ⟨π(g)e, e⟩`; III.6, printed
  p. 271 (PDF p. 37): `C(G)` is defined by the norms `ν_r(f) = sup |f(g)| Ξ(g)^{-1} (1 + σ(g))^r`.

Both statements are source content; this module removes the absolute-convergence hypothesis of
the earlier modules when `Ξ` is the spherical function `xi hP₀K δ₀`, as the source does with the
proof of Lemma VI.2.2 and Lemma II.1.5.

## Scope and hypotheses

Below, `δ_P = HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer` (the modulus of the
action of `M` on `U`).

### Xi section

Section variables, all used by the theorem:

- `G` is a locally compact, nonarchimedean, second countable, Hausdorff topological group with
  `MeasurableSpace`, `BorelSpace` and `Nonempty (CompactOpenSubgroup G)`; `P`, `M`, `U` are
  subgroups with `[LocallyCompactSpace P]`;
- `h : IsSemidirectDecomposition P M U`, `hU : IsClosed U`, `hP : IsClosed P`,
  `hm : Continuous h.projection`;
- `K : OpenSubgroup G`, `hK : IsCompact K`, `hPK : ∀ g, ∃ q ∈ P, ∃ k ∈ K, g = q k`;
  `hG` (`G` unimodular); `hδ` (the modular character of `P` is the modulus of its action on `U`);
- `A : SmoothRep ℂ M`, `hcof : CompactOpenCofinal M`; a normal subgroup `C` of `M` with
  `hC : C ≤ center M`, a measurable structure on `M/C` with `BorelSpace`, an inversion-invariant
  Haar measure `μM` on `M/C`; `hsq : IsSquareIntegrableModCentralSubgroup C hC A μM`;
  `hi : A` irreducible;
- a subgroup `P₀` with characters `δ₀ : P₀ →* ℝ≥0ˣ`, `δ₀M : P₀ ∩ M →* ℝ≥0ˣ`;
  `[CompactSpace K]`, `[CompactSpace (K ∩ M)]`; `hL : LeviData K P₀ P M δ₀ δ_P δ₀M h.projection`;
  `hP₀K : IsIwasawaPair P₀ K`; `hMKiw : IsIwasawaPair (P₀ ∩ M) (K ∩ M)`;
  `hδ₀ : ∀ p : P₀, p ∈ K → δ₀ p = 1`;
- `hcoeff` (Corollary III.1.2 for `M`): for all `v ∈ A` and smooth `ℓ` in the dual, there is
  `C > 0` with `‖ℓ(A(m) v)‖ ≤ C Ξ^M(m)` for all `m`, where `Ξ^M = xi hMKiw δ₀M`;
- a left and right invariant measure `μ` on `G` and `σ : G → ℝ` with
  `hw : L2Weights μ (xi hP₀K δ₀) σ`;
  `hT : HasTemperedCoefficients (xi hP₀K δ₀) σ (I_P^G A)`;
  `hΞ : ∀ g, xi hP₀K δ₀ g⁻¹ = xi hP₀K δ₀ g`; `hσ : ∀ g, σ g⁻¹ = σ g`;
- `hδU : IsUnimodularModulus U hU`; `[Nonempty (CompactOpenSubgroup M)]`; a left and right
  invariant measure `μL` on `M` and `ΞM σM : M → ℝ` with `hwM : L2Weights μL ΞM σM`,
  `hTM : HasTemperedCoefficients ΞM σM A`, `hΞM : ∀ m, ΞM m⁻¹ = ΞM m`,
  `hσM : ∀ m, σM m⁻¹ = σM m`;
- a left and right invariant measure `ν` on `U` with `hD : ConstantTermData ν δ_P`,
  `hν : IsConjModulus h.levi_le_normalizer ν δ_P` and
  `hE : ConstantTermEstimate ν δ_P (xi hP₀K δ₀) σ ΞM σM` (Proposition II.4.5 for the opposite
  parabolic); `ht : TranslationWeights (xi hP₀K δ₀) σ`; `htM : TranslationWeights ΞM σM`.

`inducedFourierTransform_eq_constantTermInducedFourierTransform_xi` also takes:

- `[MeasurableInv G]`, `[μ.IsInvInvariant]`, `[SigmaFinite μ]` and `hμK : μ K = 1`;
- `[MeasurableInv M]`, `[μL.IsInvInvariant]`, `[SFinite μL]` and `[SFinite ν]`;
- `hPKiw : ∀ (m : M) (u : U), m u ∈ K ↔ m ∈ K ∧ u ∈ K`;
- `hMK : μL (M ∩ K) = 1` and `hUK : ν (U ∩ K) = 1`;
- `f : Space (xi hP₀K δ₀) σ`.

These are the hypotheses of `inducedFourierTransform_eq_constantTermInducedFourierTransform` with
`Ξ = xi hP₀K δ₀`, without `hint`, plus `P₀`, `δ₀`, `δ₀M`, the two compactness instances, `hL`,
`hP₀K`, `hMKiw`, `hδ₀` and `hcoeff`.

### SmoothXi section

Section variables, all used by the definition:

- the instances on `G`, the subgroups `P`, `M`, `U` with `[LocallyCompactSpace P]`, and `h`, `hU`,
  `hP`, `hm`, `K`, `hK`, `hPK`, `hG`, `hδ` as in the Xi section;
- a type `I`, characters `ν : I → (M →* ℝ≥0ˣ)` and `π : IrreducibleAdmissibleRep ℂ M`;
  `hcof : CompactOpenCofinal M`; `C`, `hC`, the measurable structure on `M/C` and `μM` as in the
  Xi section;
- `hsq : ∀ A : UnitaryOrbitRepresentative ν π`, square integrability of `A` modulo `C` for `μM`;
- `P₀`, `δ₀`, `δ₀M`, `[CompactSpace K]`, `[CompactSpace (K ∩ M)]`, `hL`, `hP₀K`, `hMKiw`, `hδ₀`
  as in the Xi section;
- `hcoeff : ∀ A : UnitaryOrbitRepresentative ν π`, Corollary III.1.2 for `A` (every coefficient
  of `A` is bounded by a multiple of `xi hMKiw δ₀M`);
- a left and right invariant measure `μ` on `G`, `σ : G → ℝ`, `hw : L2Weights μ (xi hP₀K δ₀) σ`;
  `hT : ∀ A`, `HasTemperedCoefficients (xi hP₀K δ₀) σ (I_P^G A)`; `hΞ`, `hσ`.

`fourierOrbitSmoothSectionLinearXi` also takes:

- a finite type `J`, torus coordinates `e : unitaryUnramifiedCharacters ν ≃* (J → Circle)`,
  `hνc : ∀ i, Continuous (ν i)` and `hPK' : ∀ g, ∃ p : P, ∃ k : K, g = p k`;
- `hsqπ`: square integrability of `π` modulo `C` for `μM`;
- `[MeasurableInv G]`, `[μ.IsInvInvariant]`, `[SigmaFinite μ]`, `hμK : μ K = 1`;
  `hδU : IsUnimodularModulus U hU`; `[Nonempty (CompactOpenSubgroup M)]`;
- a measure `μL` on `M` that is left and right invariant, inversion invariant (with
  `[MeasurableInv M]`) and s-finite; `ΞM σM : M → ℝ` with `hwM : L2Weights μL ΞM σM`;
  `hTπ : HasTemperedCoefficients ΞM σM π`; `hTM : ∀ A`, `HasTemperedCoefficients ΞM σM A`;
  `hΞM`, `hσM`;
- a left and right invariant, s-finite measure `νU` on `U` with `hD : ConstantTermData νU δ_P`,
  `hνU : IsConjModulus h.levi_le_normalizer νU δ_P`,
  `hE : ConstantTermEstimate νU δ_P (xi hP₀K δ₀) σ ΞM σM`; `ht`, `htM`;
- `hPKiw`, `hMK : μL (M ∩ K) = 1`, `hUK : νU (U ∩ K) = 1`;
- the lattice map: `n : M → (J → ℤ)` with `hn : n(g h) = n(g) + n(h)`, a compact open subgroup
  `K₀` of `M` with `hK₀ : ∀ k ∈ K₀, n k = 0`, `hnm : Measurable n`,
  `hnσ : ∀ m, ‖n m‖ ≤ Cn (1 + σM m)`, and `hne : ∀ z m, χ_z(m) = torusCharacter (n m) z`, where
  `χ_z = unitaryTorusParameter ν e z`.

These are the hypotheses of `fourierOrbitSmoothSectionLinear` with `Ξ = xi hP₀K δ₀`, without
`hint`, plus `P₀`, `δ₀`, `δ₀M`, the two compactness instances, `hL`, `hP₀K`, `hMKiw`, `hδ₀` and
`hcoeff`.

## Definitions

- `fourierOrbitSmoothSectionLinearXi … : Space (xi hP₀K δ₀) σ →ₗ[ℂ]
  productInducedSmoothOrbitSections ν π e h hU K hP hK hνc hm hPK'` is `f ↦ ψ_f[O, P]`; it is
  `fourierOrbitSmoothSectionLinear` with `hint` supplied by
  `integrable_coefficientPairingIntegrand`.

## Results

- `inducedFourierTransform_eq_constantTermInducedFourierTransform_xi`: Lemma VII.1.2,
  `f̂(ω, P) = f̂^{(P),Ind}(ω)` for every `f ∈ C(G)`, for `Ξ = xi hP₀K δ₀`.

## Proof notes

1. The theorem applies `inducedFourierTransform_eq_constantTermInducedFourierTransform` with
   `hint` given by `integrable_coefficientPairingIntegrand` for each `ψ ∈ L(ω, P)`.
2. The definition applies `fourierOrbitSmoothSectionLinear` with `hint` given in the same way for
   every `f` and every representative.

## Open obligations

- `hw` (Lemma II.1.5), `hcoeff` (Corollary III.1.2), `hE` (Proposition II.4.5), the Iwasawa data,
  the lattice map `n` and the tempered coefficients remain hypotheses.
