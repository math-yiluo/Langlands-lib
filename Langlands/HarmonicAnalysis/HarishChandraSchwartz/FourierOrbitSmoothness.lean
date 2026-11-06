import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TwistedFourierIdentification
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedConstantTermFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierCoherence
import Langlands.Representation.Plancherel.FiniteSmoothCompactEvaluation
import Langlands.Representation.Induction.FiniteProductTensorBijectiveProof

/-! # Smoothness of `ψ_f[O, P]` (Waldspurger, Proposition VII.1.3)

Waldspurger, Proposition VII.1.3 (printed p. 316): for `f ∈ C(G)`, `ψ_f[O, P]` belongs to
`C^∞(O, P)`, and `f ↦ ψ_f[O, P]` is continuous. The proof: "Grâce au Lemme VII.1.2 et à la
continuité de l'application `f ↦ f^{(P)}`, on est ramené au cas `M = G`."

Here `C^∞(O, P)` is Worker 200's `productInducedSmoothOrbitSections`: coherent sections over the
representatives of the orbit of `π` under the unitary unramified characters, whose restriction to
the fixed compact picture on `K × K` is a finite smooth family in torus coordinates `e`.
`fourierOrbitSection_mem_smooth` proves that `ψ_f[O, P]` (`fourierOrbitSection`) lies there, and
`fourierOrbitSmoothSectionLinear` is the resulting linear map. The proof follows the source:
coherence is `fourierOrbitSection_mem_coherent`; at a point `(k₁, k₂)` of `K × K` the value of
`f̂(ω_z, P)` is `[f^{(P),Ind}(k₁, k₂)]^(ω_z, M)` by Lemma VII.1.2 (`eval_inducedFourierTransform`),
which is smooth in `z` by the case `M = G` (`TwistedFourierIdentification`), since
`d(ω ⊗ χ) = d(ω)` (`representationFormalDegree_unitaryTwist`). Worker 200's
`mem_finiteSmoothFamilies_of_common_open_stabilizer` assembles the values, using that all
`f̂(ω_z, P)` are right invariant under `H × H` for a compact open `H` under which `f` is
bi-invariant. The continuity assertion is not addressed: no topology on `C^∞(O, P)` is defined.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel
open Langlands.HarmonicAnalysis.TorusFourier
open scoped ComplexConjugate NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uV uI

section Smooth

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M)) (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μM : Measure (M ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : ∀ A : UnitaryOrbitRepresentative ν π,
    IsSquareIntegrableModCentralSubgroup C hC A.val.obj.representation μM)
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (hw : L2Weights μ Ξ σ)
  (hT : ∀ A : UnitaryOrbitRepresentative ν π,
    HasTemperedCoefficients Ξ σ ((normalizedInductionFunctor h hU).obj A.val.obj).representation)
  (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)

omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] in
/-- `f^{(P),Ind}` is right invariant under `H × H` when `f` is bi-invariant under `H`. -/
theorem Space.constantTermInd_mul_of_isBiInvariant [Nonempty (CompactOpenSubgroup M)]
    {ΞM σM : M → ℝ} {νU : Measure U} {δ : M →* ℝ≥0ˣ} (hD : ConstantTermData νU δ)
    (hE : ConstantTermEstimate νU δ Ξ σ ΞM σM) (ht : TranslationWeights Ξ σ)
    (htM : TranslationWeights ΞM σM) (f : Space Ξ σ) {H : Subgroup G}
    (hH : IsBiInvariant H f) {l₁ l₂ : G} (hl₁ : l₁ ∈ H) (hl₂ : l₂ ∈ H) (x : G × G) :
    Space.constantTermInd hD hE ht htM f (x.1 * l₁, x.2 * l₂) =
      Space.constantTermInd hD hE ht htM f x :=
  Space.ext fun m => congrFun (hH.constantTermInd_mul νU δ hl₁ hl₂ x) m

set_option maxHeartbeats 1000000 in
/-- **Proposition VII.1.3, smoothness** (Waldspurger, printed p. 316): for `f ∈ C(G)`,
`ψ_f[O, P]` lies in Worker 200's smooth sections `C^∞(O, P)` over the orbit of `π`, given torus
coordinates `e` on the unitary unramified characters and a lattice map `n` with
`χ_z(m) = ∏ⱼ zⱼ^{n(m)ⱼ}` for the character `χ_z` of parameter `z`. The proof reduces to `M`
by Lemma VII.1.2 and applies `TwistedFourierIdentification` on `M`. -/
theorem fourierOrbitSection_mem_smooth {J : Type*} [Fintype J]
    (e : unitaryUnramifiedCharacters ν ≃* (J → Circle)) (hνc : ∀ i, Continuous (ν i))
    (hPK' : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
    (hsqπ : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
    [MeasurableInv G] [μ.IsInvInvariant] [SigmaFinite μ] (hμK : μ (K : Set G) = 1)
    (hδU : IsUnimodularModulus U hU) [Nonempty (CompactOpenSubgroup M)]
    {μL : Measure M} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] [MeasurableInv M]
    [μL.IsInvInvariant] [SFinite μL] {ΞM σM : M → ℝ} (hwM : L2Weights μL ΞM σM)
    (hTπ : HasTemperedCoefficients ΞM σM π.obj.representation)
    (hTM : ∀ A : UnitaryOrbitRepresentative ν π,
      HasTemperedCoefficients ΞM σM A.val.obj.representation)
    (hΞM : ∀ m, ΞM m⁻¹ = ΞM m) (hσM : ∀ m, σM m⁻¹ = σM m)
    {νU : Measure U} [νU.IsMulLeftInvariant] [νU.IsMulRightInvariant] [SFinite νU]
    (hD : ConstantTermData νU (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
    (hνU : IsConjModulus h.levi_le_normalizer νU
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
    (hE : ConstantTermEstimate νU
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) Ξ σ ΞM σM)
    (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)
    (hPKiw : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μL {m : M | (m : G) ∈ K} = 1) (hUK : νU {u : U | (u : G) ∈ K} = 1)
    {n : M → J → ℤ} (hn : ∀ g h, n (g * h) = n g + n h) {K₀ : CompactOpenSubgroup M}
    (hK₀ : ∀ k ∈ K₀.toSubgroup, n k = 0) (hnm : Measurable n) {Cn : ℝ}
    (hnσ : ∀ m, ‖n m‖ ≤ Cn * (1 + σM m))
    (hne : ∀ z m, (((unitaryTorusParameter ν e z).val m : ℂˣ) : ℂ) = torusCharacter (n m) z)
    (f : Space Ξ σ)
    (hint : ∀ (A : UnitaryOrbitRepresentative ν π)
      (ψ : productInducedCoefficientObject h hU A.val.obj),
      Integrable
        (fun x : G × K => conj (CompactInduction.integrand h hU A.val.obj K x.1 ψ x.2) * f x.1)
        (μ.prod (CompactInduction.measure K hK))) :
    fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f ∈
      productInducedSmoothOrbitSections ν π e h hU K hP hK hνc hm hPK' := by
  refine ⟨fourierOrbitSection_mem_coherent h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT
    hΞ hσ f, ?_⟩
  change productInducedFamilyRestriction ν e h K hP hK hνc hm hU hPK' π.obj
      (productInducedOrbitPullback ν π e h hU
        (fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f)) ∈
    finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj)
  obtain ⟨H, hH⟩ := Space.exists_isBiInvariant f
  have : IsTopologicalGroup (K.prod K) :=
    inferInstanceAs (IsTopologicalGroup (K.prod K).toSubgroup)
  have : CompactSpace (K.prod K) := isCompact_iff_compactSpace.mp (by
    rw [OpenSubgroup.coe_prod]
    exact hK.prod hK)
  let Lo : OpenSubgroup (K.prod K) :=
    (H.1.prod H.1).comap (K.prod K).toSubgroup.subtype continuous_subtype_val
  let χ : (J → Circle) → M →* ℂˣ := fun z => (unitaryTorusParameter ν e z).val.toMonoidHom
  let hχ : ∀ z, IsOpen ((χ z).ker : Set M) := fun z =>
    unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z)
  let R : (J → Circle) → UnitaryOrbitRepresentative ν π :=
    unitaryOrbitParameterRepresentative ν π e
  let dπ := representationFormalDegree C hC μM hcof hsqπ π.property.1
  have hdeg : ∀ z, representationFormalDegree C hC μM hcof (hsq (R z)) (R z).val.property.1 =
      dπ := fun z =>
    representationFormalDegree_unitaryTwist C hC μM hcof (χ z) (hχ z)
      (fun m => by
        change ‖((χ z m : ℂˣ) : ℂ)‖ = 1
        rw [show ((χ z m : ℂˣ) : ℂ) = torusCharacter (n m) z from hne z m,
          norm_torusCharacter]) hsqπ π.property.1
  have heval : ∀ z (x : G × G),
      Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject (R z).val.obj (R z).val.obj.contragredient))
        (fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f
          (R z)) x =
      coefficientFourierTransform (R z).val.obj hwM (hsq (R z)).1 (hTM (R z)) hΞM hσM
        (representationFormalDegree C hC μM hcof (hsq (R z)) (R z).val.property.1)
        (Space.constantTermInd hD hE ht htM f x) := fun z x =>
    eval_inducedFourierTransform h hU hP hm K hK hPK hG hδ (R z).val.obj hcof C hC μM (hsq (R z))
      (R z).val.property.1 hw (hT (R z)) hΞ hσ hδU hwM (hTM (R z)) hΞM hσM hD hνU hE ht htM hμK
      hPKiw hMK hUK f (hint (R z)) x
  let E := LinearMap.pi fun k : K.prod K =>
    Induction.FiniteProductTensorBijective.evalLinear (k := ℂ)
      ((P.prod P).comap (K.prod K).toSubgroup.subtype)
      (compactPictureInducingRepresentation (h.prod h) (K.prod K)
        (productLeviObject π.obj π.obj.contragredient)) k
  have hEinj : Function.Injective E := fun F₁ F₂ h₁₂ =>
    Induction.FiniteProductTensorBijective.smoothFunctions_ext _ _ fun k => congrFun h₁₂ k
  have hval : ∀ (z : J → Circle) (k : K.prod K),
      E (productInducedFamilyRestriction ν e h K hP hK hνc hm hU hPK' π.obj
          (productInducedOrbitPullback ν π e h hU
            (fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ
              f)) z) k =
        twistTensorEquiv π.obj (χ z) (hχ z)
          (coefficientFourierTransform (π.obj.twist (χ z) (hχ z)) hwM (hsq (R z)).1
            (hTM (R z)) hΞM hσM dπ (Space.constantTermInd hD hE ht htM f (k : G × G))) :=
    fun z k => by
      refine (productInducedFamilyRestriction_eval ν e h K hP hK hνc hm hU hPK' π.obj
        (productInducedOrbitPullback ν π e h hU
          (fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f))
        z k).trans ?_
      refine (congrArg (productCompactTwistTensorEquiv ν (unitaryTorusParameter ν e z) π.obj)
        (heval z (k : G × G))).trans ?_
      rw [hdeg z]
      rfl
  refine mem_finiteSmoothFamilies_of_common_open_stabilizer E hEinj _ Lo ?_ ?_
  · intro z k l
    have hl : ((l : K.prod K) : G × G) ∈ ((H.1.prod H.1 : OpenSubgroup (G × G)) : Set (G × G)) :=
      l.2
    rw [OpenSubgroup.coe_prod] at hl
    rw [hval, hval]
    congr 2
    exact Space.constantTermInd_mul_of_isBiInvariant hD hE ht htM f hH hl.1 hl.2 (k : G × G)
  · intro k
    have heq : (fun z => E (productInducedFamilyRestriction ν e h K hP hK hνc hm hU hPK' π.obj
          (productInducedOrbitPullback ν π e h hU
            (fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ
              f)) z) k) =
        fun z => twistTensorEquiv π.obj (χ z) (hχ z)
          (coefficientFourierTransform (π.obj.twist (χ z) (hχ z)) hwM (hsq (R z)).1
            (hTM (R z)) hΞM hσM dπ (Space.constantTermInd hD hE ht htM f (k : G × G))) :=
      funext fun z => hval z k
    rw [heq]
    exact twistTensorEquiv_coefficientFourierTransform_mem_finiteSmoothFamilies π.obj hwM
      hsqπ.1 hTπ hn hK₀ hnm hnσ χ hχ (fun z m => hne z m) (fun z => (hsq (R z)).1)
      (fun z => hTM (R z)) hΞM hσM dπ (Space.constantTermInd hD hE ht htM f (k : G × G))

/-- **Waldspurger's map `C(G) → C^∞(O, P)`, `f ↦ ψ_f[O, P]`** (Proposition VII.1.3): the linear
map `f ↦ ψ_f[O, P]` into Worker 200's smooth sections over the orbit of `π`. -/
def fourierOrbitSmoothSectionLinear {J : Type*} [Fintype J]
    (e : unitaryUnramifiedCharacters ν ≃* (J → Circle)) (hνc : ∀ i, Continuous (ν i))
    (hPK' : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
    (hsqπ : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
    [MeasurableInv G] [μ.IsInvInvariant] [SigmaFinite μ] (hμK : μ (K : Set G) = 1)
    (hδU : IsUnimodularModulus U hU) [Nonempty (CompactOpenSubgroup M)]
    {μL : Measure M} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] [MeasurableInv M]
    [μL.IsInvInvariant] [SFinite μL] {ΞM σM : M → ℝ} (hwM : L2Weights μL ΞM σM)
    (hTπ : HasTemperedCoefficients ΞM σM π.obj.representation)
    (hTM : ∀ A : UnitaryOrbitRepresentative ν π,
      HasTemperedCoefficients ΞM σM A.val.obj.representation)
    (hΞM : ∀ m, ΞM m⁻¹ = ΞM m) (hσM : ∀ m, σM m⁻¹ = σM m)
    {νU : Measure U} [νU.IsMulLeftInvariant] [νU.IsMulRightInvariant] [SFinite νU]
    (hD : ConstantTermData νU (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
    (hνU : IsConjModulus h.levi_le_normalizer νU
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
    (hE : ConstantTermEstimate νU
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) Ξ σ ΞM σM)
    (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)
    (hPKiw : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μL {m : M | (m : G) ∈ K} = 1) (hUK : νU {u : U | (u : G) ∈ K} = 1)
    {n : M → J → ℤ} (hn : ∀ g h, n (g * h) = n g + n h) {K₀ : CompactOpenSubgroup M}
    (hK₀ : ∀ k ∈ K₀.toSubgroup, n k = 0) (hnm : Measurable n) {Cn : ℝ}
    (hnσ : ∀ m, ‖n m‖ ≤ Cn * (1 + σM m))
    (hne : ∀ z m, (((unitaryTorusParameter ν e z).val m : ℂˣ) : ℂ) = torusCharacter (n m) z)
    (hint : ∀ (f : Space Ξ σ) (A : UnitaryOrbitRepresentative ν π)
      (ψ : productInducedCoefficientObject h hU A.val.obj),
      Integrable
        (fun x : G × K => conj (CompactInduction.integrand h hU A.val.obj K x.1 ψ x.2) * f x.1)
        (μ.prod (CompactInduction.measure K hK))) :
    Space Ξ σ →ₗ[ℂ] productInducedSmoothOrbitSections ν π e h hU K hP hK hνc hm hPK' where
  toFun f := ⟨fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f,
    fourierOrbitSection_mem_smooth h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ
      e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm hnσ
      hne f (hint f)⟩
  map_add' f₁ f₂ := Subtype.ext <| funext fun _ => map_add _ f₁ f₂
  map_smul' c f := Subtype.ext <| funext fun _ => map_smul _ c f

end Smooth

end Langlands.HarishChandraSchwartz
