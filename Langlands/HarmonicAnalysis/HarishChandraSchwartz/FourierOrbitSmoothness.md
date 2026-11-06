# Smoothness of `ψ_f[O, P]` (Waldspurger, Proposition VII.1.3)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitSmoothness`, namespace
`Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TwistedFourierIdentification`:
  `twistTensorEquiv` and
  `twistTensorEquiv_coefficientFourierTransform_mem_finiteSmoothFamilies` (the case `M = G` in
  torus coordinates), and through its imports `Space.twist`, `torusCharacter` and
  `norm_torusCharacter`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedConstantTermFourier`:
  `eval_inducedFourierTransform` (Lemma VII.1.2 pointwise), `Space.constantTermInd`
  (`f^{(P),Ind}` in `C(M)`) and `Space.exists_isBiInvariant`; through its imports
  `IsBiInvariant.constantTermInd_mul`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierCoherence`:
  `fourierOrbitSection` (`ψ_f[O, P]`) and `fourierOrbitSection_mem_coherent`; through its
  imports Worker 200's `UnitaryOrbitRepresentative`, `unitaryOrbitParameterRepresentative`,
  `unitaryTorusParameter`, `productInducedOrbitPullback`, `productInducedFamilyRestriction` with
  `productInducedFamilyRestriction_eval`, `productCompactTwistTensorEquiv`,
  `ProductInducedCompactPicture`, `compactPictureInducingRepresentation`,
  `productInducedSmoothOrbitSections`, `unramifiedCharacter_isOpen_ker` and
  `representationFormalDegree_unitaryTwist`;
- `Langlands.Representation.Plancherel.FiniteSmoothCompactEvaluation` (Worker 200):
  `mem_finiteSmoothFamilies_of_common_open_stabilizer`;
- `Langlands.Representation.Induction.FiniteProductTensorBijectiveProof`:
  `Induction.FiniteProductTensorBijective.evalLinear` and `smoothFunctions_ext`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`).

- Proposition VII.1.3, printed p. 316 (PDF p. 82): "Pour tout `f ∈ C(G)`, la fonction
  `ψ_f[O, P]` appartient à `C^∞(O, P)`. L'application `C(G) → C^∞(O, P)`, `f ↦ ψ_f[O, P]` est
  continue." Proof: "Grâce au Lemme VII.1.2 et à la continuité de l'application `f ↦ f^{(P)}`,
  on est ramené au cas `M = G`." Then, for `M = G`: smoothness of
  `C_{v⊗v̌, f}(χ) = d(ω ⊗ χ) ⟨(ω ⊗ χ)(f̌) v, v̌⟩`, and "Notons que `d(ω ⊗ χ) = d(ω)` pour tout
  `χ ∈ Im X(G)`."
- VI.1, printed pp. 295–296 (PDF pp. 61–62): `C^∞(O, P)` and its identification with smooth
  families in the fixed space `L_K(ω, P)`.
- Lemma VII.1.2, printed p. 315 (PDF p. 81): `f̂(ω, P) = f̂^{(P),Ind}(ω)`.

The first assertion of Proposition VII.1.3 (`ψ_f[O, P] ∈ C^∞(O, P)`) is source content, as is
the linear map `f ↦ ψ_f[O, P]`. The continuity assertion is not addressed. The lemma
`Space.constantTermInd_mul_of_isBiInvariant` is derived.

### Correspondence with the source

- `O` is the orbit of the class of `π : IrreducibleAdmissibleRep ℂ M` under the unitary
  unramified characters `unitaryUnramifiedCharacters ν`, with torus coordinates
  `e : unitaryUnramifiedCharacters ν ≃* (J → Circle)` (Waldspurger's `Im X(M)`). `ω_z` is the
  literal twist of `π` by the character `χ_z = unitaryTorusParameter ν e z`
  (`unitaryOrbitParameterRepresentative ν π e z`).
- `C^∞(O, P)` is `productInducedSmoothOrbitSections ν π e h hU K hP hK hνc hm hPK'` (Worker 200):
  coherent sections whose parameter pullback, restricted to the fixed compact picture
  `ProductInducedCompactPicture h K π.obj` of functions on `K × K`, is a finite smooth family on
  `J → Circle`.
- `ψ_f[O, P]` is `fourierOrbitSection … f`, `ω ↦ f̂(ω, P)`, from `InducedFourierCoherence`.
- The lattice map `n : M → (J → ℤ)` and the identity
  `hne : χ_z(m) = torusCharacter (n m) z = ∏ⱼ zⱼ^{n(m)ⱼ}` express `χ_z` in the coordinates `z`;
  Waldspurger's unitary unramified characters are `m ↦ q^{-⟨λ, H_M(m)⟩}` with `λ` imaginary
  (I.1 and the proof of Proposition VII.1.3), which motivates this form. `n` and `hne` are
  hypotheses here.

## Scope and hypotheses

Section variables: those of the orbit section of `InducedFourierCoherence` (instances on `G`:
`Group`, `TopologicalSpace`, `LocallyCompactSpace`, `NonarchimedeanGroup`,
`SecondCountableTopology`, `T2Space`, `MeasurableSpace`, `BorelSpace`,
`Nonempty (CompactOpenSubgroup G)`; subgroups `P`, `M`, `U` with `[LocallyCompactSpace P]`; `h`,
`hU`, `hP`, `hm`, `K`, `hK`, `hPK`, `hG`, `hδ`; `ν : I → (M →* ℝ≥0ˣ)`, `π`, `hcof`; `C`, `hC`, the
measurable structure on `M/C` and an inversion-invariant Haar measure `μM`;
`hsq : ∀ A : UnitaryOrbitRepresentative ν π`, square integrability of `A` modulo `C`; a left and
right invariant measure `μ` on `G` with `hw : L2Weights μ Ξ σ`;
`hT : ∀ A`, tempered coefficients of `I_P^G A`; `hΞ`, `hσ`).

`Space.constantTermInd_mul_of_isBiInvariant` takes `[Nonempty (CompactOpenSubgroup M)]`, a
measure `νU` on `U`, a character `δ` of `M`, `hD : ConstantTermData νU δ`,
`hE : ConstantTermEstimate νU δ Ξ σ ΞM σM`, `ht`, `htM`, `f ∈ C(G)`, a subgroup `H` with
`hH : IsBiInvariant H f`, `l₁, l₂ ∈ H` and `x ∈ G × G`. It does not use local compactness, second
countability or the Hausdorff property of `G`.

`fourierOrbitSection_mem_smooth` also takes:

- a finite type `J` and torus coordinates `e : unitaryUnramifiedCharacters ν ≃* (J → Circle)`;
  `hνc : ∀ i, Continuous (ν i)`; `hPK' : ∀ g, ∃ p : P, ∃ k : K, g = p k` (Worker 200's form of
  `G = P K`);
- `hsqπ`: square integrability of `π` modulo `C` for `μM`;
- the hypotheses of Lemma VII.1.2 (`InducedConstantTermFourier`), except those attached to one
  inducing representation: `[MeasurableInv G]`, `[μ.IsInvInvariant]`, `[SigmaFinite μ]`,
  `hμK : μ K = 1`, `hδU : IsUnimodularModulus U hU`, `[Nonempty (CompactOpenSubgroup M)]`, a
  measure `μL` on `M` that is left and right invariant, inversion invariant and s-finite with
  `[MeasurableInv M]`, `hwM : L2Weights μL ΞM σM`, `hΞM`, `hσM`, a measure `νU` on `U` that is left
  and right invariant and s-finite, `hD`, `hνU`, `hE` (for
  `δ = closedRestrictCharacter U hU M …`), `ht`, `htM`, `hPKiw`, `hMK`, `hUK`;
- tempered coefficients on `M`: `hTπ` for `π`, and `hTM : ∀ A`, for every representative;
- the lattice map: `n : M → (J → ℤ)` with `hn : n(g h) = n(g) + n(h)`, a compact open subgroup
  `K₀` of `M` with `hK₀ : ∀ k ∈ K₀, n k = 0`, `hnm : Measurable n`,
  `hnσ : ∀ m, ‖n m‖ ≤ Cn (1 + σM m)`, and `hne : ∀ z m, χ_z(m) = torusCharacter (n m) z`;
- `f ∈ C(G)` and `hint : ∀ A ψ`, the absolute convergence of Lemma VII.1.2 for every
  representative `A` (for `Ξ = xi` this is `integrable_coefficientPairingIntegrand` of
  `InducedCoefficientConvergence`).

`fourierOrbitSmoothSectionLinear` takes the same hypotheses except `f`, with `hint` required for
every `f ∈ C(G)`.

## Definitions

- `fourierOrbitSmoothSectionLinear … : Space Ξ σ →ₗ[ℂ] productInducedSmoothOrbitSections ν π e h hU
  K hP hK hνc hm hPK'` is `f ↦ ψ_f[O, P]`.

## Results

- `Space.constantTermInd_mul_of_isBiInvariant`: if `f` is bi-invariant under `H` and
  `l₁, l₂ ∈ H`, then `f^{(P),Ind}(x₁ l₁, x₂ l₂) = f^{(P),Ind}(x₁, x₂)` in `C(M)`.
- `fourierOrbitSection_mem_smooth` (**Proposition VII.1.3, first assertion**):
  `ψ_f[O, P] ∈ C^∞(O, P)`.

## Proof notes

1. Coherence is `fourierOrbitSection_mem_coherent`.
2. Choose a compact open `H` under which `f` is bi-invariant. For every `z` and
   `(k₁, k₂) ∈ K × K`, the compact-picture value of `ψ_f[O, P]` at `ω_z` is the untwisted value
   `f̂(ω_z, P)(k₁, k₂)` (`productInducedFamilyRestriction_eval`). By Lemma VII.1.2
   (`eval_inducedFourierTransform` for the representative `ω_z`) this is the untwisted
   `[f^{(P),Ind}(k₁, k₂)]^(ω_z, M)` with the constant `d(ω_z)`, and `d(ω_z) = d(π)` by
   `representationFormalDegree_unitaryTwist` (`|χ_z| = 1` because `|torusCharacter| = 1`).
3. For fixed `(k₁, k₂)`, `z ↦` that value is a finite smooth family in `E ⊗ Ě` by
   `twistTensorEquiv_coefficientFourierTransform_mem_finiteSmoothFamilies` on `M`.
4. The values at `(k₁ l₁, k₂ l₂)` and `(k₁, k₂)` agree for `l₁, l₂ ∈ H`, by
   `Space.constantTermInd_mul_of_isBiInvariant`. Worker 200's
   `mem_finiteSmoothFamilies_of_common_open_stabilizer`, applied to evaluation on the compact
   group `K × K` (injective) and the open subgroup `(H × H) ∩ (K × K)`, gives the finite smooth
   family.
5. The theorem is compiled with `set_option maxHeartbeats 1000000`: the identification in step 2
   of Worker 200's untwisting map for the representative with `twistTensorEquiv` for the literal
   twist is checked by definitional unfolding.

## Relation to the Library

- This module combines Lemma VII.1.2 (`InducedConstantTermFourier`), the coherence of
  `ψ_f[O, P]` (`InducedFourierCoherence`) and the case `M = G` (`TwistedFourierIdentification`)
  with Worker 200's smooth sections `C^∞(O, P)`.

## Open obligations

- The continuity of `f ↦ ψ_f[O, P]` (second assertion of Proposition VII.1.3) is not addressed;
  no topology on `C^∞(O, P)` is defined.
- The lattice map `n` with `hne`, the absolute convergence `hint` for Waldspurger's `Ξ` (see
  `InducedCoefficientConvergence`), Proposition II.4.5 (`hE`), Lemma II.1.5 (`hw`, `hwM`), and the
  tempered coefficients `hT`, `hTM`, `hTπ` are hypotheses.
