import Langlands.BaseChange.NormalizedParabolicConstantTerm
import Langlands.Group.GL.ParabolicQuotient
import Langlands.BaseChange.TwistedVanDijk.Measures

/-! # Evaluation of the normalized twisted constant term on the ambient radical

The Library's normalized twisted constant term `normalizedTwistedParabolicConstantTerm`
integrates over the unipotent radical realized inside the parabolic. This module evaluates it
with a Haar measure `du` on the actual radical `B.unipotentSubgroup E ≤ GL_n(E)` giving `U ∩ K`
volume one and the Haar probability measure `dk` on `K = GL_n(𝒪_E)`:
`φ^{P,σ}(x) = δ_P(x)^{1/2} ∫_U ∫_K φ(k⁻¹ x u σ(k)) dk du`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure GeneralLinear HarmonicAnalysis TwistedVanDijk

universe u v

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  unipotentSubgroup_secondCountable unipotentSubgroup_locallyCompact
  parabolic_secondCountable parabolic_locallyCompact integralGL_compactSpace
  integralGL_secondCountable

variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]

/-- **Evaluation of the normalized twisted constant term with a Haar measure on the ambient
radical.** For a Haar measure `μU` on the radical `B.unipotentSubgroup E` of `GL_n(E)` giving
`U ∩ K` volume one and the Haar probability `μK` on `K = GL_n(𝒪_E)`,
`φ^{P,σ}(x) = δ_P(x)^{1/2} ∫_U ∫_K φ(k⁻¹ x u σ(k)) dk du`. -/
theorem normalizedTwistedParabolicConstantTerm_apply_unipotentSubgroup
    (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure]
    (hU : μU {y | (y : GeneralLinear n E) ∈ integralGL E n} = 1)
    (μK : Measure (integralGL E n)) [μK.IsHaarMeasure] [IsProbabilityMeasure μK]
    (φ : SchwartzBruhat (GeneralLinear n E)) (x : B.Levi E) :
    normalizedTwistedParabolicConstantTerm E B σ φ x =
      ((LocalFieldData.ofInstances E).leviHalfModulus B x : ℂ) *
        ∫ y, ∫ κ, φ ((κ : GeneralLinear n E)⁻¹ * B.leviEmbedding E x *
          (y : GeneralLinear n E) * entrywiseAut σ n κ) ∂μK ∂μU := by
  set e := B.unipotentAmbientEquivContinuous E
  have hval : ∀ y : B.unipotentSubgroup E,
      ((e.symm y : B.unipotentRadical E) : B.parabolic E).val = y.val := fun y =>
    congrArg Subtype.val (e.apply_symm_apply y)
  set μU' : Measure (B.unipotentRadical E) := μU.map e.symm
  have hμU' : μU' {u | ((u : B.parabolic E) : GeneralLinear n E) ∈
      standardMaximalCompact E n} = 1 := by
    have hmeas : MeasurableSet {u : B.unipotentRadical E |
        ((u : B.parabolic E) : GeneralLinear n E) ∈ standardMaximalCompact E n} :=
      ((isOpen_standardMaximalCompact E n).preimage
        (continuous_subtype_val.comp continuous_subtype_val)).measurableSet
    change μU.map e.symm _ = 1
    rw [Measure.map_apply (show Measurable (e.symm : B.unipotentSubgroup E → B.unipotentRadical E)
      from e.symm.continuous.measurable) hmeas]
    convert hU using 2
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hval]
  rw [normalizedTwistedParabolicConstantTerm_eq,
    normalizedAutParabolicConstantTerm_apply_of_isHaarMeasure E B _ _ μK μU' hμU' φ x]
  congr 1
  change ∫ u, (fun u : B.unipotentRadical E => ∫ κ, φ ((κ : GeneralLinear n E)⁻¹ *
      B.leviEmbedding E x * ((u : B.parabolic E) : GeneralLinear n E) * entrywiseAut σ n κ)
      ∂μK) u ∂(μU.map e.symm.toHomeomorph.toMeasurableEquiv) = _
  rw [integral_map_equiv]
  congr 1
  funext y
  change ∫ κ, φ ((κ : GeneralLinear n E)⁻¹ * B.leviEmbedding E x *
    ((e.symm y : B.unipotentRadical E) : B.parabolic E).val * entrywiseAut σ n κ) ∂μK = _
  rw [hval]

end Langlands.BaseChange.TwistedLocalDescent
