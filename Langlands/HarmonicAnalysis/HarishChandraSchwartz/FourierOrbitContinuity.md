# Continuity of `f ↦ ψ_f[O, P]` (Waldspurger, Proposition VII.1.3)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitContinuity`, namespace
`Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitLaurentSmoothness` (Worker 249):
  `fourierOrbitLaurentSmoothSectionLinear`, `isOpen_commonNormKernel_of_continuous`; through its
  imports `FourierOrbitSmoothness` (`fourierOrbitSmoothSectionLinear`, the map
  `f ↦ ψ_f[O, P]` into `C^∞(O, P)`, and `Space.constantTermInd_mul_of_isBiInvariant`),
  `LaurentExponent` (`laurentExponent`, `laurentExponent_mul`,
  `laurentExponent_eq_zero_of_isCompact`, `measurable_laurentExponent`,
  `torusCharacter_laurentExponent`), `TwistedFourierIdentification` (`twistTensorEquiv`,
  `twistTensorEquiv_schwartzActionTensor`,
  `twistTensorEquiv_coefficientFourierTransform_mem_finiteSmoothFamilies`),
  `TwistedFourierFamily` (`Space.twist`, `IsBiInvariant.twistedFunction`,
  `schwartzActionTensor_eq_sum`, `smoothDual_schwartzAction_twist`),
  `TwistedCoefficientSmoothness` (`twistedCoefficientFamily`,
  `exists_norm_torusPartialDerivList_twistedCoefficientFamily_le`: Waldspurger's estimate (2)),
  `FourierTransform` (`schwartzActionTensor`, `coefficientFourierTransform` with
  `coefficientFourierTransform_apply`), `SchwartzAction` (`continuous_coefficient`,
  `exists_nu_coefficient_ne_top`), `TraceCoefficientFamily` (`fixedFunctional`), `L2`
  (`Space.check`, `IsBiInvariant.check`, `nu_check`, `L2Weights.nonneg`), `ConstantTerm`
  (`ConstantTermData.isBiInvariant`, `ConstantTermEstimate.nu_le`), `Translations`
  (`CompactOpenSubgroup.translate`, `IsBiInvariant.translate`, `IsBiInvariant.translate_eq`,
  `TranslationWeights.nu_translate_le`, `Space.translate`), `InducedFourierTransform`
  (`inducedFourierTransform_translate`, Lemma VII.1.1 (i)), `InducedConstantTermFourier`
  (`eval_inducedFourierTransform`, Lemma VII.1.2 pointwise, and `Space.constantTermInd`),
  `InducedFourierCoherence` (`fourierOrbitSection`, `ψ_f[O, P]`), `Basic` (`Level`, `Space`,
  `Level.withSeminorms`, `Level.isBiInvariant`, `Space.ofLevel`, `Space.mkCLM`, `nu_mono`,
  `Space.nu_ne_top`), Worker 200's `productInducedFamilyRestriction_eval`,
  `productCompactTwistTensorEquiv`, `unitaryTorusParameter`, `unitaryOrbitParameterRepresentative`,
  `unramifiedCharacter_isOpen_ker`, `representationFormalDegree_unitaryTwist`,
  `productInducedOrbitRepresentation`, `mem_finiteSmoothFamilies_linearMap`, and
  `Induction.FiniteProductTensorBijective.evalLinear` with `smoothFunctions_ext`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionTopology` (Worker 249): the
  topology of `C^∞(O, P)` (`OrbitSectionSpace`, `OrbitSectionLevel`,
  `orbitSectionLevelSubmodule`, `orbitSectionLevelSubmodule_antitone`, `orbitSectionSeminorm`,
  `orbitSectionSeminorm_le_iff`, `OrbitSectionLevel.withSeminorms`,
  `OrbitSectionLevel.toSections`, `OrbitSectionSpace.ofLevel`,
  `OrbitSectionSpace.continuous_ofLevel`, `OrbitSectionSpace.toSections`) and the torus helpers
  `torusPartialDerivListLinear`, `torusPartialDerivListLinear_apply`,
  `isSmoothFiniteTorusFunction_of_mem_finiteSmoothFamilies`;
- from Mathlib: `LinearMap.exists_leftInverse_of_injective`, `QuotientGroup.mk_out_eq_mul`, the
  finiteness of the quotient of a compact group by an open subgroup, `Finset.univ_sum_single`,
  `WithSeminorms.continuous_of_isBounded` and `Seminorm.IsBounded.of_real`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234.

Proposition VII.1.3 and its proof, printed pp. 316–317 (PDF pp. 82–83): "Pour tout `f ∈ C(G)`,
la fonction `ψ_f[O, P]` appartient à `C^∞(O, P)`. L'application `C(G) → C^∞(O, P)`,
`f ↦ ψ_f[O, P]` est continue. Preuve. Grâce au Lemme VII.1.2 et à la continuité de l'application
`f ↦ f^{(P)}`, on est ramené au cas `M = G`. Fixons `(ω, E) ∈ O` et un sous-groupe ouvert compact
`H` de `G`. Pour `v ∈ E^H`, `v̌ ∈ Ě^H`, `f ∈ C_H`, `χ ∈ Im X(G)`, posons
`C_{v⊗v̌, f}(χ) = d(ω ⊗ χ)⟨(ω ⊗ χ)(f̌) v, v̌⟩`. L'énoncé résulte des assertions suivantes: […]
l'application `C_H → C^∞(Im X(G))`, `f ↦ C_{v⊗v̌, f}` est continue. […] Les propriétés ci-dessus
résultent de la majoration suivante. Soient `v ∈ E^H`, `v̌ ∈ Ě^H`, `D` un opérateur différentiel
à coefficients constants sur `Im X(G)`. Alors il existe `c > 0` et `r ∈ ℝ` tels que pour tous
`f ∈ C_H`, `∫_G |f̌(g)⟨ω(g)v, v̌⟩D(χ(g))| dg ⩽ c ν_r(f)`. (2)"

Also used: the topology of `C(G)` and its universal property III.6 (1) (printed pp. 271–272), the
topology of `C^∞(O, P)` of VI.3 (printed p. 301), Lemma VII.1.1 (i) and Lemma VII.1.2 (printed
pp. 314–316).

`fourierOrbitSectionCLM` and `fourierOrbitLaurentSectionCLM` are the second assertion of
Proposition VII.1.3 (source content) for the Library's `C(G)` (`Space Ξ σ`) and `C^∞(O, P)`
(`OrbitSectionSpace`). `continuous_fourierOrbitSectionLevelLinear` is the continuity on each
level that the source's reduction provides, and the two `exists_norm_torusPartialDerivList_…`
bounds for `M = G` are the source's assertion "`C_H → C^∞(Im X(G))`, `f ↦ C_{v⊗v̌, f}` est
continue" in seminorm form, uniform over the linear forms on `E ⊗ Ě` (see below).
`productInducedOrbitRepresentation_fourierOrbitSection` is the consequence of Lemma VII.1.1 (i)
that `ψ_f[O, P]` is fixed by `H × H` when `f` is bi-invariant under `H`, used for the source's
level-by-level argument. The remaining results (`Space.isBiInvariant_constantTermInd`,
`Space.exists_nu_constantTermInd_le`, the key estimate
`exists_norm_torusPartialDerivList_fourierOrbitSection_le`, the level membership, the level map
and the `toSections` lemmas) are derived steps of the proof.

### How the Lean statements model the source

- As in `FourierOrbitSmoothness`, `O` is the orbit of `π` under `unitaryUnramifiedCharacters ν`
  with torus coordinates `e`, the characters are `χ_z = unitaryTorusParameter ν e z`, and a
  lattice map `n` with `hne : χ_z(m) = ∏ⱼ zⱼ^{n(m)ⱼ}` writes them in coordinates; in
  `fourierOrbitLaurentSectionCLM`, `n = laurentExponent ν e he`.
- The constant-coefficient operators `D` are the iterated angle derivatives `∂_l`
  (`torusPartialDerivList`), as in `TwistedCoefficientSmoothness`.
- Waldspurger works with `v ∈ E^H`, `v̌ ∈ Ě^H`, i.e. with the coordinates of
  `f̂(ω) ∈ E^H ⊗ Ě^H`. The topology of `C^∞(O, P)` in `OrbitSectionTopology` uses all linear forms
  `ℓ` on the compact picture `L_K`; correspondingly, the `M = G` bounds are stated for an arbitrary
  linear form `lam` on `A ⊗ Ã` (`CoefficientTensor A`). The proof writes `π(f χ_z)` for `f`
  bi-invariant under a fixed `K'` in a basis of the finite-dimensional `A^{K' ∩ K₀}`
  (`schwartzActionTensor_eq_sum`), so `lam` only sees finitely many coordinates.
- The general case: on the compact picture, the values `E(F)(k)` at `k ∈ K × K` of an element
  `F` right invariant under `H × H` are determined by the values at representatives of the finite
  quotient `(K × K)/((H × H) ∩ (K × K))`, so every linear form on such elements is a finite sum of
  linear forms of these values. At a value, Lemma VII.1.2 gives
  `[f^{(P),Ind}(k₁, k₂)]^(ω_z, M)` with `d(ω_z) = d(π)`, and `f^{(P),Ind}(k₁, k₂)` is
  bi-invariant under the compact open subgroup `(k₁ H k₁⁻¹ ∩ k₂ H k₂⁻¹) ∩ M` of `M`, independent
  of `f`.
- The level `C_H` of `C(G)` is mapped into the level of `C^∞(O, P)` for `H ∩ K`, because the
  inductive limit of `OrbitSectionTopology` runs over the open subgroups contained in `K`.

## Scope and hypotheses

Section `LevelBound` (the variables of the family section of `TwistedFourierIdentification`): a
group `G` with a topology, `[IsTopologicalGroup G]`, `[MeasurableSpace G]`,
`[OpensMeasurableSpace G]`, `[MeasurableMul G]`, `[Nonempty (CompactOpenSubgroup G)]`; a left and
right invariant measure `μ`; weights `Ξ σ : G → ℝ`; `A : SmoothRep ℂ G` with
`hw : L2Weights μ Ξ σ`, `hA : IsAdmissible A.representation`,
`hT : HasTemperedCoefficients Ξ σ A.representation`; a finite type `J` with `[DecidableEq J]`;
`n : G → (J → ℤ)` with `hn : n(g h) = n(g) + n(h)`, a compact open subgroup `K₀` with
`hK₀ : ∀ k ∈ K₀, n k = 0`, `hnm : Measurable n`, `hnσ : ∀ g, ‖n g‖ ≤ C (1 + σ g)`.

- `exists_norm_torusPartialDerivList_schwartzActionTensor_twist_le` takes these, a compact open
  subgroup `K'`, a linear form `lam : Module.Dual ℂ (CoefficientTensor A)` and a list `l`.
- `exists_norm_torusPartialDerivList_twistTensorEquiv_coefficientFourierTransform_le` also takes
  `χ : (J → Circle) → G →* ℂˣ` with `hχ : ∀ z, IsOpen (ker χ_z)`,
  `hχn : ∀ z g, χ_z(g) = torusCharacter (n g) z`, `hA' : ∀ z`, admissibility of `A ⊗ χ_z`,
  `hT' : ∀ z`, tempered coefficients of `A ⊗ χ_z`, `hΞ : ∀ g, Ξ g⁻¹ = Ξ g`,
  `hσ : ∀ g, σ g⁻¹ = σ g`, and a real `d` (the constant of the Fourier transform).

Section `ConstantTermBounds`: a group `G` with a topology, `[IsTopologicalGroup G]`,
`[MeasurableSpace G]`, `[BorelSpace G]`, `[Nonempty (CompactOpenSubgroup G)]`; subgroups `M`, `U`; a
measure `νU` on `U`, `δ : M →* ℝ≥0ˣ`, weights `Ξ σ` on `G` and `ΞM σM` on `M`;
`hD : ConstantTermData νU δ`, `hE : ConstantTermEstimate νU δ Ξ σ ΞM σM`,
`ht : TranslationWeights Ξ σ`, `htM : TranslationWeights ΞM σM`.
`Space.isBiInvariant_constantTermInd` takes a compact open `H`, `f` with
`hf : IsBiInvariant H f` and `g ∈ G × G`; `Space.exists_nu_constantTermInd_le` takes `g` and `s`.

Section `Orbit`: the section variables of `FourierOrbitSmoothness` (instances on `G`: `Group`,
`TopologicalSpace`, `LocallyCompactSpace`, `NonarchimedeanGroup`, `SecondCountableTopology`,
`T2Space`, `MeasurableSpace`, `BorelSpace`, `Nonempty (CompactOpenSubgroup G)`; subgroups `P`,
`M`, `U` with `[LocallyCompactSpace P]`; `h : IsSemidirectDecomposition P M U`, `hU`, `hP`,
`hm : Continuous h.projection`, an open subgroup `K` with `hK : IsCompact K`,
`hPK : ∀ g, ∃ q ∈ P, ∃ k ∈ K, g = q k`, `hG`, `hδ`; `ν : I → (M →* ℝ≥0ˣ)`,
`π : IrreducibleAdmissibleRep ℂ M`, `hcof : CompactOpenCofinal M`; a normal subgroup `C` with
`hC : C ≤ center M`, a measurable and Borel structure on `M/C` and an inversion-invariant Haar
measure `μM`; `hsq : ∀ A : UnitaryOrbitRepresentative ν π`, square integrability modulo `C`; a
left and right invariant measure `μ` on `G` with `hw : L2Weights μ Ξ σ`; `hT : ∀ A`, tempered
coefficients of `I_P^G A`; `hΞ`, `hσ`).

- `productInducedOrbitRepresentation_fourierOrbitSection` takes these, `ht : TranslationWeights Ξ σ`,
  a subgroup `H`, `f` with `hf : IsBiInvariant H f`, and `x ∈ G × G` with `x.1, x.2 ∈ H`.
- All later results take, in addition, the hypotheses of `fourierOrbitSmoothSectionLinear`: a
  finite type `J` (with `[DecidableEq J]`, omitted where the statement has no derivative), torus
  coordinates `e`, `hνc : ∀ i, Continuous (ν i)`, `hPK' : ∀ g, ∃ p : P, ∃ k : K, g = p k`,
  `hsqπ` (square integrability of `π` modulo `C`), `[MeasurableInv G]`, `[μ.IsInvInvariant]`,
  `[SigmaFinite μ]`, `hμK : μ K = 1`, `hδU : IsUnimodularModulus U hU`,
  `[Nonempty (CompactOpenSubgroup M)]`, a left and right invariant, inversion invariant, s-finite
  measure `μL` on `M` with `[MeasurableInv M]`, `hwM : L2Weights μL ΞM σM`, `hTπ`, `hTM : ∀ A`
  (tempered coefficients on `M`), `hΞM`, `hσM`, a left and right invariant s-finite measure `νU`
  on `U`, `hD`, `hνU : IsConjModulus … νU δ`, `hE` (for `δ = closedRestrictCharacter U hU M …`),
  `ht`, `htM`, `hPKiw`, `hMK`, `hUK`, the lattice map `n` with `hn`, `K₀`, `hK₀`, `hnm`,
  `hnσ : ∀ m, ‖n m‖ ≤ Cn (1 + σM m)`, `hne : ∀ z m, χ_z(m) = torusCharacter (n m) z`, and
  `hint : ∀ f A ψ`, the absolute convergence of Lemma VII.1.2 for every `f ∈ C(G)` and every
  representative `A`.
- `fourierOrbitSmoothSectionLinear_mem_orbitSectionLevelSubmodule`: an open subgroup `H` and `f`
  with `hf : IsBiInvariant H f`.
- `exists_norm_torusPartialDerivList_fourierOrbitSection_le`: a compact open subgroup `H`, a list
  `l` and a linear form `ℓ` on `ProductInducedCompactPicture h K π.obj`.
- `fourierOrbitSectionLevelLinear`, `toSections_fourierOrbitSectionLevelLinear`,
  `continuous_fourierOrbitSectionLevelLinear`: a compact open subgroup `H` (and `f`).
- `fourierOrbitLaurentSectionCLM`, `toSections_fourierOrbitLaurentSectionCLM`: the hypotheses of
  `fourierOrbitLaurentSmoothSectionLinear`, i.e. the above without `n`, `hn`, `K₀`, `hK₀`, `hnm`,
  `hnσ`, `hne`, and with `he : HasLaurentUnitaryCoordinates ν e` and
  `hlσ : ∀ m, ‖laurentExponent ν e he m‖ ≤ Cl (1 + σM m)` (and `f`).

## Definitions

- `fourierOrbitSectionLevelLinear … H : Level Ξ σ H →ₗ[ℂ] OrbitSectionLevel … (H ∩ K)`, `f ↦ ψ_f[O, P]`
  on the level `C_H` of `C(G)`.
- `fourierOrbitSectionCLM … : Space Ξ σ →L[ℂ] OrbitSectionSpace ν π e h hU K hP hK hνc hm hPK'`, the
  map `f ↦ ψ_f[O, P]` (`fourierOrbitSmoothSectionLinear`) as a continuous linear map.
- `fourierOrbitLaurentSectionCLM … he hlσ`, the same with `n = laurentExponent ν e he`; its
  underlying linear map is `fourierOrbitLaurentSmoothSectionLinear`.

## Results

- `exists_norm_torusPartialDerivList_schwartzActionTensor_twist_le`: there are `s`, `c` with
  `|∂_l (z ↦ lam(π(f χ_z)))(z)| ≤ c ν_s(f)` for all `z` and all `f ∈ C(G)` bi-invariant under
  `K'`, where `π(f χ_z) = schwartzActionTensor A … (Space.twist hn hK₀ z f)`.
- `exists_norm_torusPartialDerivList_twistTensorEquiv_coefficientFourierTransform_le`
  (**Proposition VII.1.3 for `M = G`, continuity in seminorm form on a level**): there are `s`, `c`
  with `|∂_l (z ↦ lam(twistTensorEquiv ((A ⊗ χ_z)^(d)(f))))(z)| ≤ c ν_s(f)` for all `z` and all
  `f` bi-invariant under `K'`, where `(A ⊗ χ_z)^(d)(f) = d · (A ⊗ χ_z)(f̌)` is
  `coefficientFourierTransform`.
- `Space.isBiInvariant_constantTermInd`: for `f` bi-invariant under `H`, `f^{(P),Ind}(g₁, g₂)` is
  bi-invariant under `(H.translate g₁ g₂).subgroupOf hD.isClosed`
  (`(g₁ H g₁⁻¹ ∩ g₂ H g₂⁻¹) ∩ M`).
- `Space.exists_nu_constantTermInd_le`: there are `s'` and `c ≥ 0` with
  `ν^M_s(f^{(P),Ind}(g₁, g₂)) ≤ c ν_{s'}(f)` for all `f ∈ C(G)`.
- `productInducedOrbitRepresentation_fourierOrbitSection`: `x · ψ_f[O, P] = ψ_f[O, P]` for
  `x ∈ H × H` and `f` bi-invariant under `H`.
- `fourierOrbitSmoothSectionLinear_mem_orbitSectionLevelSubmodule`: `ψ_f[O, P]` lies in the level
  `C^∞(O, P)^{H×H}`.
- `exists_norm_torusPartialDerivList_fourierOrbitSection_le` (**key estimate**): there are `s`, `c`
  with `|∂_l (y ↦ ℓ(R ψ_f[O, P] y))(z)| ≤ c ν_s(f)` for all `z` and all `f` bi-invariant under
  `H`, where `R = productInducedSmoothOrbitCompactRestriction`.
- `toSections_fourierOrbitSectionLevelLinear`: the level map is `f ↦ ψ_f[O, P]`.
- `continuous_fourierOrbitSectionLevelLinear` (**Proposition VII.1.3, continuity on a level**).
- `toSections_fourierOrbitSectionCLM`, `fourierOrbitSectionCLM_apply_val`: the continuous linear
  map is `f ↦ ψ_f[O, P]` (by `rfl`); with `fourierOrbitSectionCLM` itself this is the
  **second assertion of Proposition VII.1.3**.
- `toSections_fourierOrbitLaurentSectionCLM`: the Laurent version is
  `fourierOrbitLaurentSmoothSectionLinear`.

## Proof notes

1. `M = G`. Let `K = K' ∩ K₀` and `b` a basis of the finite-dimensional `A^K` (admissibility),
   `ℓᵢ = fixedFunctional (b.coord i)`. For `f` bi-invariant under `K'`, `f χ_z` is bi-invariant
   under `K` (`IsBiInvariant.twistedFunction`), so `schwartzActionTensor_eq_sum` and
   `smoothDual_schwartzAction_twist` give
   `lam(π(f χ_z)) = ∑_{i,j} lam(b_j ⊗ ℓᵢ) Φ_{ij}(f)(z)`, where `Φ_{ij}` is the
   `twistedCoefficientFamily` of the coefficient `g ↦ ℓ_j(A(g) bᵢ)`. The derivative `∂_l` is linear
   on smooth torus functions (`torusPartialDerivListLinear`), and each `∂_l Φ_{ij}(f)` is bounded
   by `exists_norm_torusPartialDerivList_twistedCoefficientFamily_le` (estimate (2)). The indices
   are combined with `s = ∑ |s_{ij}|` and `nu_mono` (`σ ≥ 0` from `L2Weights`). For the Fourier
   transform, `coefficientFourierTransform_apply` and `twistTensorEquiv_schwartzActionTensor` turn
   `lam(twistTensorEquiv((A ⊗ χ_z)^(d)(f)))` into `(d · lam)(π(f̌ χ_z))`; `f̌` is bi-invariant under
   `K'` and `ν_s(f̌) = ν_s(f)` (`nu_check`).
2. `Space.isBiInvariant_constantTermInd`: `IsBiInvariant.translate` and
   `ConstantTermData.isBiInvariant`. `Space.exists_nu_constantTermInd_le`:
   `ConstantTermEstimate.nu_le` composed with `TranslationWeights.nu_translate_le`.
3. `productInducedOrbitRepresentation_fourierOrbitSection`: at each representative,
   `inducedFourierTransform_translate` and `ρ(x₁)λ(x₂) f = f` (`IsBiInvariant.translate_eq`).
4. Key estimate. As in `FourierOrbitSmoothness`, `E` is evaluation of the compact picture on
   `K × K` (injective), and Lemma VII.1.2 with `d(ω_z) = d(π)` gives
   `E(R ψ_f z)(k) = twistTensorEquiv((π ⊗ χ_z)^(d(π))(f^{(P),Ind}(k)))` (`hval`). Let `Lo` be
   `(H × H) ∩ (K × K)`, `Q = (K × K)/Lo` (finite, since `K × K` is compact and `Lo` open), and
   `W` the submodule of compact-picture elements `F` with `E(F)(k x) = E(F)(k)` for `x ∈ Lo`. By
   `Space.constantTermInd_mul_of_isBiInvariant`, `R ψ_f z ∈ W`. Evaluation at the representatives
   `q.out` is an injective linear map `Φ : W → (Q → E ⊗ Ě)` (`QuotientGroup.mk_out_eq_mul`), with a
   linear left inverse `Ψ` (`LinearMap.exists_leftInverse_of_injective`); hence on `W`,
   `ℓ(F) = ∑_q lam_q(E(F)(q.out))` with `lam_q = ℓ ∘ Ψ ∘ Pi.single q` (`Finset.univ_sum_single`).
   Each summand `z ↦ lam_q(…)` is smooth
   (`twistTensorEquiv_coefficientFourierTransform_mem_finiteSmoothFamilies`), so `∂_l` of the sum
   is the sum of the `∂_l`; each is bounded by step 1 on the level of
   `(q.out.1 H q.out.1⁻¹ ∩ q.out.2 H q.out.2⁻¹) ∩ M` (step 2) and then by
   `Space.exists_nu_constantTermInd_le`; the indices are combined as in step 1.
5. Level map: `LinearMap.codRestrict` of `f ↦ ψ_f[O, P]` to the level of `H ∩ K` (step 3 and
   `orbitSectionLevelSubmodule_antitone`). Continuity: `WithSeminorms.continuous_of_isBounded`
   between `Level.withSeminorms` and `OrbitSectionLevel.withSeminorms`, each target seminorm
   `orbitSectionSeminorm (l, ℓ)` being bounded by `max c 0 · ν_s` (step 4 and
   `orbitSectionSeminorm_le_iff`).
6. `fourierOrbitSectionCLM` is `Space.mkCLM` (III.6 (1)) applied to
   `fourierOrbitSmoothSectionLinear`; on the level `C_H` it is
   `OrbitSectionSpace.ofLevel (H ∩ K) ∘ fourierOrbitSectionLevelLinear H`, continuous by step 5
   and `OrbitSectionSpace.continuous_ofLevel`. `fourierOrbitLaurentSectionCLM` instantiates the
   lattice map as in `fourierOrbitLaurentSmoothSectionLinear`.
7. The key estimate is compiled with `set_option maxHeartbeats 2000000`.

## Open obligations

- As in `FourierOrbitSmoothness` and `FourierOrbitLaurentSmoothness`: the lattice map `n` with
  `hne` (or the growth bound `hlσ` for `laurentExponent`), the absolute convergence `hint`,
  Proposition II.4.5 (`hE`), Lemma II.1.5 (`hw`, `hwM`), the translation estimates (`ht`, `htM`) and
  the tempered coefficients (`hT`, `hTM`, `hTπ`) are hypotheses.
- The identification of the topology of `C^∞(O, P)` with Waldspurger's product topology is not
  formalized (see `OrbitSectionTopology`).
