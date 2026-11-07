# Pairings with wave packets detect `f̂(ω, P)` (Waldspurger, proof of Corollary VII.2.3)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketOrthogonality`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketPairing` (Worker 249):
formula (1) of the proof of Proposition VII.2.2
(`pairing_inducedOrbitWavePacket_eq_integral_productPairing`), its converse direction
`pairing_inducedOrbitWavePacket_eq_zero` and the weighted orbit product
`unitaryOrbitWeightedProductPairing`. Through its imports it uses the wave packet
`inducedOrbitWavePacket` (`OrbitWavePacket`), the section `fourierOrbitSection` (`ψ_f[O, P]`,
`InducedFourierCoherence`), `pairing`, `Space Ξ σ`, `L2Weights` and `HasTemperedCoefficients`
(`TemperedPairing`), and, from Worker 200's `ProductInducedOrbitForm` and the modules below it, the
section space `productInducedSmoothOrbitSections` (`C^∞(O, P)`), the positive form
`unitaryOrbitRepresentativeProductForm` on `L(ω, P)` at a representative, the scalar orbit pairing
`unitaryOrbitProductPairing` with `unitaryOrbitProductPairing_representative`,
`continuous_unitaryOrbitProductPairing` and `integrable_unitaryOrbitProductPairing`, the unweighted
orbit core `productInducedSmoothOrbitCore` with `productInducedSmoothOrbitCore_inner_integral`,
the orbit map `discreteSeriesOrbitMap` with `continuous_discreteSeriesOrbitMap` and
`isOpenQuotientMap_discreteSeriesOrbitMap`, the orbit measure `discreteSeriesOrbitMeasure`, and
`unitaryOrbitRepresentativeDiscreteSeriesOrbit`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. The quoted displays below carry no overline in the printed text.

- Corollary VII.2.3, printed p. 319 (PDF p. 85): "Soient `P = MU`, `P' = M'U'` deux
  sous-groupes paraboliques semi-standards de `G`, `O ⊂ E_2(M)` une orbite pour l'action de
  `Im X(M)`, `ω' ∈ E_2(M')` et `ψ ∈ C^∞(O; P)`. Supposons `M'` non conjugué à `M`. Alors
  `f̂_ψ(ω', P') = 0`."
- Its proof, printed p. 319: "Notons `O'` l'orbite de `ω'` pour l'action de `Im X(M')`. Soit
  `ψ' ∈ C^∞(O'; P')`. D'après le (i) de la proposition précédente et la formule (1) de sa preuve
  on a l'égalité `∫_{O'} µ(ω'') (ψ'_{ω''}, f̂_ψ(ω'', P')) dω'' = 0`. Cette égalité valant pour
  tout `ψ'`, elle entraîne `f̂_ψ(ω'', P') = 0` pour tout `ω'' ∈ O'`."
- Formula (1) of the proof of Proposition VII.2.2, printed p. 319:
  `(f_{ψ'}, f_ψ)_G = ∫_{O'} µ(ω') (ψ'_{ω'}, f̂_ψ(ω', P')) dω'`. It is the Library's
  `pairing_inducedOrbitWavePacket_eq_integral_productPairing` (with a weight `w` in place of `µ`).
- VII.2, printed p. 319, after Corollary VII.2.3: for `ψ, ψ' ∈ C^∞(Θ)_inv`,
  `(ψ', ψ) = Σ_{(O, P = MU) ∈ Θ} c(G|M)^{-2} γ(G|M)^{-1} |W^M| |W^G|^{-1} |P(M)|^{-1}
  ∫_O µ(ω) (ψ'[O, P]_ω, ψ[O, P]_ω) dω`. "Cela définit un produit hermitien défini positif
  invariant par `G × G` sur `C^∞(Θ)_inv`."

Correspondence and generalizations:

- The source's last step is implicit. The Lean proof takes `ψ'` to be the section
  `ψ_f[O, P]` itself, which lies in `C^∞(O, P)` by Proposition VII.1.3 (printed p. 316; here the
  hypothesis `hsm`); the hypothesis then says `∫_O u(ω) (ψ_f[O, P]_ω, ψ_f[O, P]_ω) dω = 0`, and the
  definiteness of the weighted product gives `ψ_f[O, P] = 0`.
- Roles: the source's orbit `O'`, parabolic `P'`, test section `ψ'` and function `f_ψ` are the
  Lean orbit `O` (of the class of `π`), the subgroup `P = M U`, the section `q` and an arbitrary
  `f ∈ C(G)` with smooth section `ψ_f[O, P]`. The source's hypothesis, the vanishing of
  `∫_{O'} µ(ω'') (ψ'_{ω''}, f̂_ψ(ω'', P')) dω''` for every `ψ'`, enters through formula (1) as
  `(f_{ψ'}, f)_G = 0` for every wave packet `f_{ψ'}` (hypothesis `h0`). The source derives this
  vanishing from Proposition VII.2.2 (i), which is not in the Library; this module does not prove
  it.
- The weight `u` is a real, bounded, continuous, strictly positive function on the orbit in place
  of the Plancherel density `µ` of V.2, which is not in the Library. The measure on the orbit is the
  orbit measure of a finite measure `ρ` on the unitary unramified characters that is positive on
  nonempty open sets (Waldspurger: a Haar measure, finite since the group is compact).
- `unitaryOrbitWeightedProductCore` is the summand of the VII.2 hermitian product for one pair
  `(O, P)`, with `u` in place of `µ`. Positive definiteness on this summand is the content of the
  source's sentence "Cela définit un produit hermitien défini positif" restricted to one orbit; the
  constants `c(G|M)^{-2} γ(G|M)^{-1} |W^M| |W^G|^{-1} |P(M)|^{-1}`, the sum over `Θ`, the
  restriction to `C^∞(Θ)_inv` and the `G × G` invariance are not treated.
- The orbit `O` is the quotient `Im X(M) / S` of the unitary unramified characters by the
  stabilizer `S` of the class of `π` (`discreteSeriesOrbit`); a function on `O` is not identified
  with a function on `Im X(M)`.
- Derived results, not statements of the paper: `isOpenPosMeasure_discreteSeriesOrbitMeasure`,
  the four pointwise properties of `unitaryOrbitProductPairing`,
  `integrable_ofReal_mul_unitaryOrbitProductPairing`, `unitaryOrbitWeightedProductCore_inner`,
  `unitaryOrbitWeightedProductCore_one_inner` and the converse half of the final equivalence,
  which is `pairing_inducedOrbitWavePacket_eq_zero`.

## Scope and hypotheses

`isOpenPosMeasure_discreteSeriesOrbitMeasure` is stated outside the section: a group `G` with a
topology and `[NonarchimedeanGroup G]`, a type `I`, `ν : I → (G →* ℝ≥0ˣ)`, a normal subgroup `A`
of `G` with `hA : A ≤ center G`, `[MeasurableSpace (G ⧸ A)]`, a Haar measure `mu` on `G ⧸ A`, a
class `omega : DiscreteSeriesClass A hA mu` with `[Finite (discreteSeriesStabilizer A hA mu ν
omega)]`, and a measure `ρ` on `unitaryUnramifiedCharacters ν` with `[ρ.IsOpenPosMeasure]`.

Section variables (section `Orthogonality`): a group `G` with a topology,
`[LocallyCompactSpace G]`, `[NonarchimedeanGroup G]`, `[SecondCountableTopology G]`,
`[T2Space G]`, `[MeasurableSpace G]`, `[BorelSpace G]`, `[Nonempty (CompactOpenSubgroup G)]`;
subgroups `P`, `M`, `U` of `G` with `[LocallyCompactSpace P]`;
`h : IsSemidirectDecomposition P M U`, `hU : IsClosed U`, `hP : IsClosed P`; an open subgroup
`K` with `hK : IsCompact K` and `hPK : ∀ g, ∃ p : P, ∃ k : K, g = p k`;
`hG : ∀ g, modularCharacter g = 1`;
`hδ : ∀ p : P, modularCharacter p = closedRestrictCharacter U hU P … p`; a type `I`,
`ν : I → (M →* ℝ≥0ˣ)` with `hν : ∀ i, Continuous (ν i)`; `π : IrreducibleAdmissibleRep ℂ M`;
`hr : Continuous h.projection`; a finite type `J` and torus coordinates
`e : unitaryUnramifiedCharacters ν ≃* (J → Circle)`; a subgroup `P₀` with `δ₀ : P₀ →* ℝ≥0ˣ` and
`δ₀M : P₀ ∩ M →* ℝ≥0ˣ`; `[CompactSpace K]` and `[CompactSpace (K ∩ M)]`;
`hcof : CompactOpenCofinal M`; a normal subgroup `C` of `M` with `hC : C ≤ center M`,
`[MeasurableSpace (M ⧸ C)]`, `[BorelSpace (M ⧸ C)]`, a Haar measure `μ` on `M ⧸ C` with
`[μ.IsInvInvariant]` and `hsq : IsSquareIntegrableModCentralSubgroup C hC π μ`, so that the orbit
`O` is `discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)`; `[Finite S]` for the
stabilizer `S = discreteSeriesStabilizer …` of the class of `π`;
`[Finite (M ⧸ (commonNormKernel ν ⊔ C))]`; a measure `ρ` on `unitaryUnramifiedCharacters ν`; and a
real weight `u : O → ℝ`. Each statement contains only the variables it mentions, and the `omit`
lists remove instances it does not use.

- The four pointwise lemmas `unitaryOrbitProductPairing_add_left`,
  `unitaryOrbitProductPairing_smul_left` (with a scalar `c : ℂ`),
  `unitaryOrbitProductPairing_conj_symm` and `re_unitaryOrbitProductPairing_self_nonneg`: sections
  `q q' r` (as needed) and a class `ω ∈ O`; `[T2Space G]`, `[Nonempty (CompactOpenSubgroup G)]`,
  `[CompactSpace K]`, `[CompactSpace (K ∩ M)]`, `[Finite S]` and
  `[Finite (M ⧸ (commonNormKernel ν ⊔ C))]` are omitted.
- `integrable_ofReal_mul_unitaryOrbitProductPairing`: `[IsFiniteMeasure ρ]`,
  `he : Continuous e`, `hu : Continuous u`, a real `b` with `hub : ∀ ω, |u ω| ≤ b`, and sections
  `q r`.
- `unitaryOrbitWeightedProductPairing_self_eq_zero_iff`: `[IsFiniteMeasure ρ]`,
  `[ρ.IsOpenPosMeasure]`, `he`, `hu`, `hupos : ∀ ω, 0 < u ω`, a real `b` with
  `hub : ∀ ω, u ω ≤ b`, and a section `r`.
- `unitaryOrbitWeightedProductCore` (definition) and `unitaryOrbitWeightedProductCore_inner`:
  `[IsFiniteMeasure ρ]`, `[ρ.IsOpenPosMeasure]`, `he`, `hu`, `hupos`, `b`, `hub` (and sections
  `q r` for the lemma).
- `unitaryOrbitWeightedProductCore_one_inner`: `[IsFiniteMeasure ρ]`, `[ρ.IsOpenPosMeasure]`,
  `he` and sections `q r`; the weight is `1` with bound `b = 1`.
- In these, `[T2Space G]`, `[Nonempty (CompactOpenSubgroup G)]`, `[CompactSpace K]` and
  `[CompactSpace (K ∩ M)]` are omitted.

Section `Corollary` adds: `hP₀K : IsIwasawaPair P₀ K`; a measure `μG` on `G` with
`[μG.IsMulLeftInvariant]`, `[μG.IsMulRightInvariant]`, `[MeasurableInv G]`, `[μG.IsInvInvariant]`;
`σ : G → ℝ` with `hwt : L2Weights μG Ξ σ`, where `Ξ = xi hP₀K δ₀`;
`hT : ∀ A, HasTemperedCoefficients Ξ σ (I_P^G A)` for every representative
`A : UnitaryOrbitRepresentative ν π`; `hΞ : ∀ g, Ξ g⁻¹ = Ξ g`; `hσ : ∀ g, σ g⁻¹ = σ g`. Both
theorems of this section have the hypotheses `[SFinite μG]`, `[IsFiniteMeasure ρ]`,
`[ρ.IsOpenPosMeasure]`, `hLaurent : HasLaurentUnitaryCoordinates ν e`, `he : Continuous e`,
`hu : Continuous u`, `hupos : ∀ ω, 0 < u ω`, a real `b` with `hub : ∀ ω, u ω ≤ b`, the
hypotheses of Lemma VI.2.2 — `hδU : IsUnimodularModulus U hU`,
`hL : LeviData K P₀ P M δ₀ (closedRestrictCharacter U hU M …) δ₀M h.projection`,
`hMK : IsIwasawaPair (P₀ ∩ M) (K ∩ M)`, `hδ₀ : ∀ p : P₀, p ∈ K → δ₀ p = 1`,
`hcoeff : ∀ v ℓ, ∃ c > 0, ∀ m, ‖ℓ(π(m) v)‖ ≤ c Ξ^M(m)` with `Ξ^M = xi hMK δ₀M` (the conclusion of
Corollary III.1.2 for `π`) — an element `f : Space Ξ σ` and
`hsm : fourierOrbitSection … f ∈ productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK`
(the smoothness of `ψ_f[O, P]`, Proposition VII.1.3). The first theorem also has
`h0 : ∀ q, pairing μG (inducedOrbitWavePacket … ρ (fun ω => (u ω : ℂ)) q) f = 0`.

## Definitions

- `unitaryOrbitWeightedProductCore … ρ u he hu hupos hub :
  InnerProductSpace.Core ℂ (productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)`,
  with inner product `⟪q, r⟫ = ∫_O u(ω) (q_ω, r_ω) dω`, that is
  `unitaryOrbitWeightedProductPairing … ρ (fun ω => (u ω : ℂ)) q r`, where `(q_ω, r_ω)` is
  `unitaryOrbitProductPairing … q r ω` and `dω` is the orbit measure
  `discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ`. As for every
  `InnerProductSpace.Core`, it is conjugate-linear in the first argument, additive, hermitian,
  with nonnegative real part on the diagonal, and definite.

## Results

Write `f_ψ = inducedOrbitWavePacket … ρ (fun ω => (u ω : ℂ)) q` for the wave packet of a section
`q ∈ C^∞(O, P)`, `(φ₁, φ₂)_G = pairing μG φ₁ φ₂` and `f̂(A, P) = fourierOrbitSection … f A` for a
representative `A`.

- `isOpenPosMeasure_discreteSeriesOrbitMeasure`: the orbit measure
  `discreteSeriesOrbitMeasure ν A hA mu omega ρ` is positive on nonempty open sets.
- `unitaryOrbitProductPairing_add_left`: `((q + q')_ω, r_ω) = (q_ω, r_ω) + (q'_ω, r_ω)`, precisely
  `unitaryOrbitProductPairing … (q + q') r ω = unitaryOrbitProductPairing … q r ω +
  unitaryOrbitProductPairing … q' r ω`.
- `unitaryOrbitProductPairing_smul_left`: `((c • q)_ω, r_ω) = conj c (q_ω, r_ω)`.
- `unitaryOrbitProductPairing_conj_symm`: `conj (r_ω, q_ω) = (q_ω, r_ω)`.
- `re_unitaryOrbitProductPairing_self_nonneg`: `0 ≤ Re (r_ω, r_ω)`.
- `integrable_ofReal_mul_unitaryOrbitProductPairing`: `ω ↦ u(ω) (q_ω, r_ω)` is integrable for the
  orbit measure.
- `unitaryOrbitWeightedProductPairing_self_eq_zero_iff`:
  `∫_O u(ω) (r_ω, r_ω) dω = 0 ↔ r = 0`.
- `unitaryOrbitWeightedProductCore_inner`: the inner product of the core is
  `unitaryOrbitWeightedProductPairing … ρ (fun ω => (u ω : ℂ)) q r` (by definition).
- `unitaryOrbitWeightedProductCore_one_inner`: for `u = 1`, the inner product equals that of
  `productInducedSmoothOrbitCore … he ρ`.
- `fourierOrbitSection_eq_zero_of_forall_pairing_inducedOrbitWavePacket_eq_zero` (**the
  deduction in the proof of Corollary VII.2.3**): `fourierOrbitSection … f = 0`, that is
  `f̂(A, P) = 0` for every representative `A` of every class of `O`.
- `fourierOrbitSection_eq_zero_iff_forall_pairing_inducedOrbitWavePacket_eq_zero`:
  `fourierOrbitSection … f = 0 ↔ ∀ q, (f_ψ, f)_G = 0`.

## Proof notes

1. Orbit measure: `discreteSeriesOrbitMeasure` is `|S|⁻¹` times the image of `ρ` under the orbit
   map; the map is continuous and surjective (`continuous_discreteSeriesOrbitMap`,
   `isOpenQuotientMap_discreteSeriesOrbitMap`), so `Continuous.isOpenPosMeasure_map` applies, and
   `Measure.isOpenPosMeasure_smul` with the nonzero factor `|S|⁻¹`.
2. Pointwise lemmas: unfold `unitaryOrbitProductPairing` (the form
   `unitaryOrbitRepresentativeProductForm` at a chosen representative) and use the corresponding
   field of that `InnerProductSpace.Core` (`add_left`, `smul_left`, `conj_inner_symm`,
   `re_inner_nonneg`).
3. Integrability: `Integrable.bdd_mul` with `integrable_unitaryOrbitProductPairing` and the bound
   `|u| ≤ b`.
4. Definiteness: the real part of `∫ u (r, r)` is `∫ u Re (r, r)` (`integral_re`); the integrand
   is continuous (`continuous_unitaryOrbitProductPairing`) and nonnegative, so
   `integral_eq_zero_iff_of_nonneg` gives it is zero almost everywhere and
   `Continuous.ae_eq_iff_eq` (the orbit measure is positive on open sets, step 1) gives it is zero
   everywhere. Since `u > 0`, `Re (r_A, r_A)_A = 0` at every representative `A`
   (`unitaryOrbitProductPairing_representative`); the imaginary part vanishes by hermitian
   symmetry, and `definite` of the positive form gives `r.val A = 0`. The converse uses
   `smul_left` with `c = 0`.
5. The core: each field is the integral of the pointwise lemma of step 2 (`integral_conj`,
   `integral_add` with step 3, `integral_const_mul`, `integral_nonneg`); `definite` is step 4.
6. `u = 1`: `productInducedSmoothOrbitCore_inner_integral` and `one_mul`.
7. The deduction: apply `pairing_inducedOrbitWavePacket_eq_integral_productPairing` with `q` and
   `r` both equal to the smooth section `⟨ψ_f[O, P], hsm⟩` and `w = u` (so `conj ∘ w = u`); `h0`
   makes the left side `0`, and step 4 gives `ψ_f[O, P] = 0`.
8. The equivalence: one direction is step 7, the other `pairing_inducedOrbitWavePacket_eq_zero`.

## Relation to the Library

- `productInducedSmoothOrbitCore` (`ProductInducedOrbitForm`, Worker 200) is the unweighted
  positive core `∫_O (q_ω, r_ω) dω` on `C^∞(O, P)`;
  `unitaryOrbitWeightedProductCore_one_inner` identifies it with the weighted core for `u = 1`.
  The weighted core is needed to state the wave-packet hypothesis with the weight of the wave
  packet.
- `isOpenPosMeasure_unitaryOrbitParameterMeasure` (`ProductInducedOrbitForm`) is the analogous
  fact for the torus-cover measure; `isOpenPosMeasure_discreteSeriesOrbitMeasure` is the fact for
  the orbit measure itself.
- The smoothness hypothesis `hsm` is supplied by `fourierOrbitSection_mem_smooth_of_hasLaurent`
  (`FourierOrbitLaurentSmoothness`, Proposition VII.1.3 with Laurent coordinates) under its
  hypotheses.

## Open obligations

- Corollary VII.2.3 itself is not proved: the vanishing hypothesis `h0` for wave packets on a
  non-conjugate Levi subgroup is Proposition VII.2.2 (i), which is not in the Library. The source
  proves it from Lemma VII.1.2 (in the Library with explicit analytic hypotheses,
  `inducedFourierTransform_eq_constantTermInducedFourierTransform` in `InducedConstantTermFourier`)
  and Proposition VI.4.1 (i) (not in the Library).
- The Plancherel density `µ` (V.2) is not in the Library; `u` stands in for it.
- The hermitian product on `C^∞(Θ)_inv` (the sum over `Θ` with its constants) and its `G × G`
  invariance are not formalized.
- `hcoeff` (Corollary III.1.2 for `π`), the Iwasawa and Levi data `hL`, `hP₀K`, `hMK`, `hδ₀`, the
  temperedness `hT` and the smoothness `hsm` are hypotheses.
