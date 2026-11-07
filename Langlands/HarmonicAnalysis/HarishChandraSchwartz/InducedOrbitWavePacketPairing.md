# The pairing of a wave packet with `C(G)` (Waldspurger, proof of Proposition VII.2.2)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketPairing`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacket` (Worker 249): the wave packet
  `inducedOrbitWavePacket`, Lemma VI.2.2 `exists_norm_unitaryOrbitCoefficientMap_le_xi` and
  `isFiniteMeasure_discreteSeriesOrbitMeasure`; through its imports Worker 200's
  `unitaryOrbitCoefficientMap` (`E_P^G ψ_ω`) with `unitaryOrbitCoefficientMap_representative` and
  `continuous_unitaryOrbitCoefficient` (Lemma VI.2.1 (i)), the section space
  `productInducedSmoothOrbitSections` (`C^∞(O, P)`), `UnitaryOrbitRepresentative`,
  `unitaryOrbitRepresentativeDiscreteSeriesOrbit` with its surjectivity, the orbit measure
  `discreteSeriesOrbitMeasure`, and `xi`, `IsIwasawaPair`, `LeviData`, `continuous_xi`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierCoherence` (Worker 249):
  `fourierOrbitSection` (`ψ_f[O, P]`); through its imports
  `integral_conj_coefficientMap_mul_eq_inner` (Lemma VII.1.1 (ii), `InducedFourierTransform`), the space `Space Ξ σ` (`C(G)`), `pairing`,
  `L2Weights`, `HasTemperedCoefficients` and `Space.integrable_mul` (`TemperedPairing`);
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientConvergence`:
  `nu_zero_ofReal_le_one`;
- `Langlands.Representation.Plancherel.ProductInducedOrbitForm` (Worker 200):
  `unitaryOrbitRepresentativeProductForm` (the product of V.2 on `L(ω, P)` at a representative),
  `unitaryOrbitProductPairing` (the scalar pairing on the orbit) and
  `unitaryOrbitProductPairing_representative`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. In the quotations, `conj(z)` transcribes the overline (complex conjugation) of
the printed text.

- Proof of Proposition VII.2.2, printed p. 319 (PDF p. 85): "On a l'égalité
  `(f_{ψ'}, f_ψ)_G = ∫_G ∫_{O'} µ(ω') conj((E^G_{P'} ψ'_{ω'})(g)) dω' f_ψ(g) dg`. D'après le
  Lemme VI.2.2, l'intégrale double est absolument convergente. On obtient
  `(f_{ψ'}, f_ψ)_G = ∫_{O'} µ(ω') (E^G_{P'} ψ'_{ω'}, f_ψ)_G dω'`, d'où, d'après le Lemme
  VII.1.1 (ii), `(f_{ψ'}, f_ψ)_G = ∫_{O'} µ(ω') (ψ'_{ω'}, f̂_ψ(ω', P')) dω'`. (1)"
- Lemma VII.1.1 (ii), printed p. 314 (PDF p. 80): `(E^G_P ψ, f)_G = (ψ, f̂(ω, P))` for
  `f ∈ C(G)` and `ψ ∈ L(ω, P)`. It is the Library's `integral_conj_coefficientMap_mul_eq_inner`.
- VII.2, printed p. 319 (PDF p. 85), after Corollary VII.2.3: for `ψ, ψ' ∈ C^∞(Θ)_inv`,
  `(ψ', ψ) = Σ_{(O, P = MU) ∈ Θ} c(G|M)^{-2} γ(G|M)^{-1} |W^M| |W^G|^{-1} |P(M)|^{-1}
  ∫_O µ(ω) (ψ'[O, P]_ω, ψ[O, P]_ω) dω`.

Correspondence and generalizations:

- The Lean statements take the second function to be any `f ∈ C(G)`, not only `f = f_ψ`. The
  source argument uses nothing about `f` beyond `f ∈ C(G)`.
- The wave packet `inducedOrbitWavePacket` (`OrbitWavePacket`) uses an arbitrary weight
  `w : O → ℂ` in place of the Plancherel density `µ` of V.2, which is not in the Library, and an
  arbitrary finite measure `ρ` on the unitary unramified characters (Waldspurger: a Haar measure).
  The pairing `(φ₁, φ₂)_G = ∫_G conj(φ₁(g)) φ₂(g) dg` is conjugate-linear in `φ₁`, so `w` appears
  as `conj (w ω)` in formula (1). For the real density `µ`, `conj µ = µ` and the formula is the
  source's.
- `pairing_inducedOrbitWavePacket_eq_integral` is the first step, the Fubini step after the
  absolute convergence of the double integral, which is
  `integrable_pairing_inducedOrbitWavePacket_integrand`.
- Formula (1) is `pairing_inducedOrbitWavePacket_eq_integral_inner`, with the integrand evaluated
  at an arbitrary choice `s(ω)` of representative of each class `ω` of the orbit. The value of
  `f̂(ω, P)` at a representative is `fourierOrbitSection … f (s ω)`.
- `pairing_inducedOrbitWavePacket_eq_integral_productPairing` is formula (1) for the scalar
  pairing on the orbit. It holds when `ψ_f[O, P]` is the underlying function of a smooth section
  `r`, which is Proposition VII.1.3 (printed p. 316). The integral is
  `unitaryOrbitWeightedProductPairing` with weight `conj ∘ w`.
- `unitaryOrbitWeightedProductPairing … w q r` is the integral
  `∫_O w(ω) (ψ'_ω, ψ_ω) dω` from the VII.2 definition of the hermitian product on
  `C^∞(Θ)_inv`, with `ψ' = q` and `ψ = r`, the weight `w` in place of `µ`, and the orbit measure of
  `ρ`. The weighted sum over `Θ` is not formed here.
- Derived results, not statements of the paper: `factorization_mem_of_subtype` (a change of
  formulation of `G = P K`), `pairing_conj_symm` (`(φ₂, φ₁)_G = conj (φ₁, φ₂)_G`), the
  representative and orbit forms of Lemma VII.1.1 (ii) for sections
  (`pairing_unitaryOrbitCoefficientMap_representative`,
  `pairing_unitaryOrbitCoefficientMap_eq_productPairing`), formula (1) in the other order
  (`pairing_inducedOrbitWavePacket_right_eq_integral_productPairing`, from
  `(f, f_ψ)_G = conj (f_ψ, f)_G`; the source uses this symmetry in the last step of (i)), and the
  vanishing
  `pairing_inducedOrbitWavePacket_eq_zero`, a direct consequence of formula (1).

## Scope and hypotheses

Section variables (section `Pairing`, those of `OrbitWavePacket` and
`InducedFourierCoherence`): a group `G` with a topology, `[LocallyCompactSpace G]`,
`[NonarchimedeanGroup G]`, `[SecondCountableTopology G]`, `[T2Space G]`, `[MeasurableSpace G]`,
`[BorelSpace G]`, `[Nonempty (CompactOpenSubgroup G)]`; subgroups `P`, `M`, `U` of `G` with
`[LocallyCompactSpace P]`; `h : IsSemidirectDecomposition P M U`, `hU : IsClosed U`,
`hP : IsClosed P`; an open subgroup `K` with `hK : IsCompact K` and
`hPK : ∀ g, ∃ p : P, ∃ k : K, g = p k`; `hG : ∀ g, modularCharacter g = 1`;
`hδ : ∀ p : P, modularCharacter p = closedRestrictCharacter U hU P … p`; a type `I`,
`ν : I → (M →* ℝ≥0ˣ)` with `hν : ∀ i, Continuous (ν i)`; `π : IrreducibleAdmissibleRep ℂ M`;
`hr : Continuous h.projection`; a finite type `J` and torus coordinates
`e : unitaryUnramifiedCharacters ν ≃* (J → Circle)`; a subgroup `P₀` with `δ₀ : P₀ →* ℝ≥0ˣ` and
`δ₀M : P₀ ∩ M →* ℝ≥0ˣ`; `[CompactSpace K]` and `[CompactSpace (K ∩ M)]`;
`hcof : CompactOpenCofinal M`; the orbit data, a normal subgroup `C` of `M` with
`hC : C ≤ center M`, `[MeasurableSpace (M ⧸ C)]`, `[BorelSpace (M ⧸ C)]`, a Haar measure `μ` on
`M ⧸ C` with `[μ.IsInvInvariant]` and `hsq : IsSquareIntegrableModCentralSubgroup C hC π μ`, so
that the orbit `O` is `discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)`;
`[Finite S]` for the stabilizer `S = discreteSeriesStabilizer …` of the class of `π`; a measure
`ρ` on `unitaryUnramifiedCharacters ν` and a weight `w : O → ℂ`;
`hP₀K : IsIwasawaPair P₀ K`; a measure `μG` on `G` with `[μG.IsMulLeftInvariant]`,
`[μG.IsMulRightInvariant]`, `[MeasurableInv G]`, `[μG.IsInvInvariant]`; `σ : G → ℝ` with
`hwt : L2Weights μG Ξ σ`, where `Ξ = xi hP₀K δ₀`; `hT : ∀ A, HasTemperedCoefficients Ξ σ (I_P^G A)`
for every representative `A`; `hΞ : ∀ g, Ξ g⁻¹ = Ξ g` and `hσ : ∀ g, σ g⁻¹ = σ g`. Each statement
contains only the variables it mentions. The `omit` lists remove the unused instances from the
statements below that do not use them.

The hypotheses of Lemma VI.2.2 (those of `exists_norm_unitaryOrbitCoefficientMap_le_xi`):
`hδU : IsUnimodularModulus U hU`;
`hL : LeviData K P₀ P M δ₀ (closedRestrictCharacter U hU M …) δ₀M h.projection`;
`hMK : IsIwasawaPair (P₀ ∩ M) (K ∩ M)`; `hδ₀ : ∀ p : P₀, p ∈ K → δ₀ p = 1`; and
`hcoeff : ∀ v ℓ, ∃ c > 0, ∀ m, ‖ℓ(π(m) v)‖ ≤ c Ξ^M(m)` with `Ξ^M = xi hMK δ₀M` (the conclusion
of Corollary III.1.2 for `π`). The hypotheses of the integrability statement are `[SFinite μG]`,
`[IsFiniteMeasure ρ]`, `hLaurent : HasLaurentUnitaryCoordinates ν e`, `he : Continuous e`,
`hwm : AEStronglyMeasurable w (discreteSeriesOrbitMeasure … ρ)`, a real `b` with
`hwb : ∀ ω, ‖w ω‖ ≤ b`, the hypotheses of Lemma VI.2.2 above, `hP₀K`, `hwt`, a section
`q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK` and `f : Space Ξ σ`. Below
they are called the *integrability hypotheses*.

- `factorization_mem_of_subtype`: a group `G` with a topology, a subgroup `P`, an open subgroup
  `K` and `hPK : ∀ g, ∃ p : P, ∃ k : K, g = p k`.
- `pairing_conj_symm`: a measurable space `G`, a measure `μ` and functions `φ₁ φ₂ : G → ℂ`; no
  integrability.
- `pairing_unitaryOrbitCoefficientMap_representative`: `hcof`, the orbit data, `hP₀K`, the
  invariance instances of `μG`, `hwt`, `hT`, `hΞ`, `hσ`, a section `q`, `f : Space Ξ σ` and a
  representative `A : UnitaryOrbitRepresentative ν π`; `[Finite S]` and `[CompactSpace (K ∩ M)]`
  are not used.
- `pairing_unitaryOrbitCoefficientMap_eq_productPairing`: the same without `A`, two sections
  `q r`, `hrf : r.val = fourierOrbitSection … f` and a class `ω ∈ O`.
- `integrable_pairing_inducedOrbitWavePacket_integrand`: the integrability hypotheses. The
  invariance instances of `μG` and `[BorelSpace (M ⧸ C)]`, `[μ.IsInvInvariant]` are not used.
- `pairing_inducedOrbitWavePacket_eq_integral`: the integrability hypotheses, with the same
  instances omitted.
- `pairing_inducedOrbitWavePacket_eq_integral_inner`: the integrability hypotheses, `hcof`, the
  invariance instances of `μG`, `hT`, `hΞ`, `hσ`, a choice
  `s : O → UnitaryOrbitRepresentative ν π` and `hs : ∀ ω, (class of s ω) = ω`.
- `unitaryOrbitWeightedProductPairing` (definition): `hcof`, the orbit data, `[Finite S]`, `ρ`,
  `w` and two sections `q r`.
- `pairing_inducedOrbitWavePacket_eq_integral_productPairing` and
  `pairing_inducedOrbitWavePacket_right_eq_integral_productPairing`: the integrability
  hypotheses, `hcof`, the invariance instances of `μG`, `hT`, `hΞ`, `hσ`, a second section `r` and
  `hrf : r.val = fourierOrbitSection … f`.
- `pairing_inducedOrbitWavePacket_eq_zero`: the integrability hypotheses, `hcof`, the invariance
  instances of `μG`, `hT`, `hΞ`, `hσ` and `hf : fourierOrbitSection … f = 0`.

## Definitions

- `unitaryOrbitWeightedProductPairing … ρ w q r : ℂ`,
  `∫_O w(ω) (q_ω, r_ω) dω` for the orbit measure
  `discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ`, where
  `(q_ω, r_ω)` is `unitaryOrbitProductPairing … q r ω`.

## Results

Write `f_ψ = inducedOrbitWavePacket … ρ w q`, `(E_P^G ψ_ω)(g) = unitaryOrbitCoefficientMap … q ω g`,
`dω` for the orbit measure and `(φ₁, φ₂)_G = pairing μG φ₁ φ₂`.

- `factorization_mem_of_subtype`: `∀ g, ∃ q ∈ P, ∃ k ∈ K, g = q k`.
- `pairing_conj_symm`: `(φ₂, φ₁)_G = conj (φ₁, φ₂)_G`.
- `pairing_unitaryOrbitCoefficientMap_representative`: for the class `ω` of `A`,
  `(E_P^G ψ_ω, f)_G = (ψ_A, f̂(A, P))_A`, with `ψ_A = q.val A`, `f̂(A, P)` the value
  `fourierOrbitSection … f A` and `( , )_A` the form `unitaryOrbitRepresentativeProductForm … A`.
- `pairing_unitaryOrbitCoefficientMap_eq_productPairing`:
  `(E_P^G ψ_ω, f)_G = unitaryOrbitProductPairing … q r ω`.
- `integrable_pairing_inducedOrbitWavePacket_integrand`: the function
  `(g, ω) ↦ conj(w(ω)) (conj((E_P^G ψ_ω)(g)) f(g))` is integrable for `μG × dω`.
- `pairing_inducedOrbitWavePacket_eq_integral`:
  `(f_ψ, f)_G = ∫_O conj(w(ω)) (E_P^G ψ_ω, f)_G dω`.
- `pairing_inducedOrbitWavePacket_eq_integral_inner` (**formula (1)**):
  `(f_ψ, f)_G = ∫_O conj(w(ω)) (ψ_{s(ω)}, f̂(s(ω), P))_{s(ω)} dω`.
- `pairing_inducedOrbitWavePacket_eq_integral_productPairing` (**formula (1)**, orbit form):
  `(f_ψ, f)_G = unitaryOrbitWeightedProductPairing … ρ (conj ∘ w) q r`, that is
  `∫_O conj(w(ω)) (ψ_ω, ψ_f[O, P]_ω) dω`.
- `pairing_inducedOrbitWavePacket_right_eq_integral_productPairing`:
  `(f, f_ψ)_G = unitaryOrbitWeightedProductPairing … ρ w r q`, that is
  `∫_O w(ω) (ψ_f[O, P]_ω, ψ_ω) dω`.
- `pairing_inducedOrbitWavePacket_eq_zero`: if `f̂(A, P) = 0` for every representative `A`, then
  `(f_ψ, f)_G = 0`.

## Proof notes

1. `factorization_mem_of_subtype`: unpack the subtypes.
2. `pairing_conj_symm`: `integral_conj`, then pointwise `conj (conj a * b) = conj b * a`.
3. Representative form: `unitaryOrbitCoefficientMap_representative` rewrites `E_P^G ψ_ω` at the
   class of `A` as the coefficient of `q.val A` for `I_P^G A`, and
   `integral_conj_coefficientMap_mul_eq_inner` (Lemma VII.1.1 (ii)) gives the product with
   `f̂(A, P)`. The final `exact` needs `set_option maxRecDepth 10000` and
   `set_option maxHeartbeats 1000000`.
4. Orbit form: choose a representative of `ω`
   (`unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective`), apply step 3 and
   `unitaryOrbitProductPairing_representative`, and rewrite with `hrf`.
5. Integrability (Lemma VI.2.2): `exists_norm_unitaryOrbitCoefficientMap_le_xi` gives `c` with
   `‖(E_P^G ψ_ω)(g)‖ ≤ c Ξ(g)`. `Space.integrable_mul` with `φ = Ξ` (continuous by `continuous_xi`,
   `ν_0(Ξ) ≤ 1` by `nu_zero_ofReal_le_one`) gives `f Ξ ∈ L¹(μG)`. The integrand is dominated by
   `|b| c ‖f(g) Ξ(g)‖`, which is integrable on `G × O` because the orbit measure is finite
   (`isFiniteMeasure_discreteSeriesOrbitMeasure`). Joint measurability of `(g, ω) ↦ (E_P^G ψ_ω)(g)`
   is `measurable_uncurry_of_continuous_of_measurable`, from continuity in `g` and continuity in
   `ω` (`continuous_unitaryOrbitCoefficient`, which uses `hLaurent` and `he`). The measurability
   of `w` is `hwm`.
6. Fubini: pointwise `conj(f_ψ(g)) f(g) = ∫_O conj(w(ω)) conj((E_P^G ψ_ω)(g)) f(g) dω`
   (`integral_conj`, `integral_mul_const`), then `integral_integral_swap` with step 5, and
   `integral_const_mul` inside.
7. Formula (1) with representatives: step 6, then step 3 at `s(ω)` rewritten with `hs ω`.
8. Formula (1) on the orbit: step 6, then step 4 at every `ω`; the integral is the definition of
   `unitaryOrbitWeightedProductPairing`.
9. Other order: `pairing_conj_symm`, step 8 and `integral_conj`; at each class, after choosing a
   representative, `conj (conj (w ω) (q_A, r_A)_A) = w(ω) (r_A, q_A)_A` by `conj_inner_symm` of
   the positive form.
10. Vanishing: step 6, then step 3 and `hf` make every integrand `conj(w(ω)) (ψ_A, 0)_A = 0`.

## Relation to the Library

- For `w = 1` and a finite measure `ρ` positive on open sets,
  `unitaryOrbitWeightedProductPairing … ρ (fun _ => 1) q r` equals, by `one_mul`, the integral in
  `productInducedSmoothOrbitCore_inner_integral` (Worker 200's positive core on `C^∞(O, P)`).
- `rationalOrbitWavePacket` and `integral_conj_mul_rationalOrbitWavePacket`
  (`RationalOrbitWavePacketPairing`, Worker 249) are Proposition VII.2.1 for `M = G` with the I.1
  orbit measure, on sections given by coefficient tensors of chosen representatives. This module
  treats formula (1) of the proof of Proposition VII.2.2 for a general `P = M U` with Worker 200's
  `C^∞(O, P)`.
- `pairing_swap` (`L2`) is the symmetry for elements of `C(G)`; `pairing_conj_symm` holds for all
  functions, as needed for the wave packet `f_ψ`, which is not shown to lie in `C(G)` here.
- The hypothesis `hrf` is supplied by `fourierOrbitSection_mem_smooth_of_hasLaurent`
  (`FourierOrbitLaurentSmoothness`, Proposition VII.1.3 with Laurent coordinates) under its
  hypotheses.

## Open obligations

- The Plancherel density `µ` (V.2) is not in the Library; `w` stands in for it.
- The weighted sum over `Θ` defining `( , )` on `C^∞(Θ)_inv`, and the remaining parts of
  Proposition VII.2.2 (the vanishing for non-conjugate `M'` via Lemma VII.1.2 and Proposition
  VI.4.1 (i), and formula (ii) via Lemma VII.1.4 and Proposition VII.2.1), are not addressed.
- `hcoeff` (Corollary III.1.2 for `π`), the Iwasawa and Levi data `hL`, `hP₀K`, `hMK`, `hδ₀`, the
  temperedness `hT` and the smoothness `hrf` are hypotheses.
