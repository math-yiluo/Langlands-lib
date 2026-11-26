import Langlands.BaseChange.TwistedVanDijk.Diagonal
import Langlands.BaseChange.TwistedVanDijk.LevelExistence
import Langlands.BaseChange.TwistedVanDijk.BlockTrace
import Langlands.BaseChange.TwistedVanDijkStatement

/-! # The twisted van Dijk formula

`twistedVanDijk` proves `TwistedVanDijkStatement` (Henniart–Lemaire 2011, II.4.5 (2)). The
trace of `π(φ) ∘ ι(A)` is computed on the finite-dimensional space of vectors fixed by a level
of `φ`, where the operator factors through functions on the cosets of the level; by cyclicity
of the trace it becomes the trace of a block operator, whose diagonal entries add up to
`(A₁ ⊗ ⋯ ⊗ A_r) ∘ τ(φ^{P,σ} ∘ σ) = τ(φ^{P,σ}) ∘ (A₁ ⊗ ⋯ ⊗ A_r)`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedVanDijk

open MeasureTheory Measure GeneralLinear HarmonicAnalysis
open scoped ENNReal NNReal

universe u v uW

section Assembly

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
  {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {P : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (W i)}
  (hP : ∀ i, IsAdmissible (P i)) (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i))

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace
  unipotentSubgroup_secondCountable unipotentSubgroup_locallyCompact
  parabolic_secondCountable parabolic_locallyCompact integralGL_compactSpace
  integralGL_secondCountable

variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)]
  (μM : Measure (B.Levi E)) [μM.IsHaarMeasure]

omit [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)] in
/-- The tensor product of block σ-intertwiners transports the integrated Levi action of
`ψ ∘ σ` to that of `ψ`. -/
theorem leviTensorIntertwiner_comp_integratedAction (ψ : SchwartzBruhat (B.Levi E)) :
    (leviTensorIntertwiner σ B A).toLinearMap ∘ₗ
        Hecke.integratedAction μM (B.blockTensor P) (FiniteTensor.isAdmissible_external P hP).1
          (Hecke.TestFunction.pullback (leviContinuousAut σ B).toHomeomorph ψ) =
      Hecke.integratedAction μM (B.blockTensor P) (FiniteTensor.isAdmissible_external P hP).1 ψ
        ∘ₗ (leviTensorIntertwiner σ B A).toLinearMap := by
  set τ := B.blockTensor P
  set hτ := (FiniteTensor.isAdmissible_external P hP).1
  set Aₜ := (leviTensorIntertwiner σ B A).toLinearMap
  apply LinearMap.ext
  intro v
  apply Module.eval_apply_injective ℂ
  apply LinearMap.ext
  intro Λ
  simp only [Module.Dual.eval_apply, LinearMap.comp_apply]
  have h1 := Hecke.integratedAction_dual μM τ hτ
    (Hecke.TestFunction.pullback (leviContinuousAut σ B).toHomeomorph ψ) v (Λ ∘ₗ Aₜ)
  have h2 := Hecke.integratedAction_dual μM τ hτ ψ (Aₜ v) Λ
  rw [LinearMap.comp_apply] at h1
  rw [h1, h2]
  have hpt : ∀ m : B.Levi E,
      (Hecke.TestFunction.pullback (leviContinuousAut σ B).toHomeomorph ψ) m *
        (Λ ∘ₗ Aₜ) (τ m v) =
      ψ (leviContinuousAut σ B m) * Λ (τ (leviContinuousAut σ B m) (Aₜ v)) := by
    intro m
    rw [Hecke.TestFunction.pullback_apply, LinearMap.comp_apply]
    congr 2
    exact LinearMap.congr_fun ((leviTensorIntertwiner σ B A).isIntertwining' m) v
  simp_rw [hpt]
  have hmeas : MeasurableEmbedding (leviContinuousAut σ B) :=
    (leviContinuousAut σ B).toHomeomorph.isClosedEmbedding.measurableEmbedding
  rw [← hmeas.integral_map (fun m' => ψ m' * Λ (τ m' (Aₜ v))), map_leviAut_eq σ B μM]

variable (μG : Measure (GeneralLinear n E)) [μG.IsHaarMeasure]
  (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure]
  (μK : Measure (integralGL E n)) [μK.IsHaarMeasure] [IsProbabilityMeasure μK]

/-- The twisted van Dijk formula for normalized measures. -/
theorem twistedDistribution_inducedSigmaIntertwiner
    (hG : μG (integralGL E n) = 1)
    (hM : μM {x | ∀ i, x i ∈ integralGL E (B.size i)} = 1)
    (hU : μU {y | (y : GeneralLinear n E) ∈ integralGL E n} = 1)
    (φ : SchwartzBruhat (GeneralLinear n E)) (ψ : SchwartzBruhat (B.Levi E))
    (hψ : ∀ x : B.Levi E, ψ x = ((LocalFieldData.ofInstances E).leviHalfModulus B x : ℂ) *
      ∫ y, ∫ κ, φ ((κ : GeneralLinear n E)⁻¹ * B.leviEmbedding E x *
        (y : GeneralLinear n E) * entrywiseAut σ n κ) ∂μK ∂μU) :
    twistedDistribution μG ((LocalFieldData.ofInstances E).normalizedProductInduced B P)
        (isAdmissible_normalizedProductInduced B P hP)
        (inducedSigmaIntertwiner σ B A).toLinearMap φ =
      twistedDistribution μM (B.blockTensor P) (FiniteTensor.isAdmissible_external P hP)
        (leviTensorIntertwiner σ B A).toLinearMap ψ := by
  classical
  obtain ⟨L⟩ := exists_level σ φ
  set hπ := isAdmissible_normalizedProductInduced B P hP
  set hτ := FiniteTensor.isAdmissible_external P hP
  let Wfix := fixedVectors ((LocalFieldData.ofInstances E).normalizedProductInduced B P)
    (L.K' : Subgroup (GeneralLinear n E))
  have : FiniteDimensional ℂ Wfix := hπ.2 L.K'
  have hbi : φ ∈ Hecke.TestFunction.biInvariant (L.K' : Subgroup (GeneralLinear n E))
      (L.K' : Subgroup (GeneralLinear n E)) :=
    ⟨fun k x => L.left k k.property x, fun l x => L.right x l l.property⟩
  let T0 := Hecke.integratedAction μG ((LocalFieldData.ofInstances E).normalizedProductInduced
    B P) hπ.1 φ
  let ι := (inducedSigmaIntertwiner σ B A).toLinearMap
  have hrange : (T0 ∘ₗ ι).range ≤ Wfix :=
    (LinearMap.range_comp_le_range _ _).trans
      (Hecke.integratedAction_range_le_fixedVectors μG _ hπ.1 hbi)
  rw [twistedDistribution_apply, FiniteRankEnd.trace_eq_subspace _ Wfix hrange]
  -- The restriction to the fixed vectors factors through functions on the cosets.
  let R' : Wfix →ₗ[ℂ] (L.Cosets → PiTensorProduct ℂ W) :=
    { toFun := fun ξ x => Induction.eval (B.parabolic E)
          (twist ((LocalFieldData.ofInstances E).parabolicHalfModulus B)
            ((B.blockTensor P).comp (B.leviProjection E))) ξ.1 (L.rep x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let S'' : (L.Cosets → PiTensorProduct ℂ W) →ₗ[ℂ] Wfix :=
    (compactOperator σ B μU μM hP A μK L).codRestrict Wfix
      (compactOperator_mem_fixedVectors σ B μU μM hP A μK L)
  have hfact : FiniteRankEnd.onSubspace (T0 ∘ₗ ι) Wfix hrange = S'' ∘ₗ R' := by
    apply LinearMap.ext
    intro ξ
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact eval_integratedAction_inducedSigmaIntertwiner σ B hP A μG μM μU μK hG hM hU L
      ξ.1 ξ.2 g
  refine (congrArg (LinearMap.trace ℂ Wfix) hfact).trans ?_
  rw [← FiniteRankEnd.trace_ofFactorization S'' R']
  -- The block operator.
  let c : ℂ := (μK.real (L.inner : Set (integralGL E n)) : ℂ)
  let Kmat : L.Cosets → L.Cosets → finiteRankEnd (PiTensorProduct ℂ W) := fun x y =>
    c • ⟨kernelOperator σ B μU μM hP A L (L.rep x) (L.rep y),
      ((Character.finiteRankIntegratedAction μM (B.blockTensor P) hτ
        (kernelTest σ B μU L (L.rep x) (L.rep y))).property.comp_left _)⟩
  have hblock : FiniteRankEnd.ofFactorization S'' R' = FiniteRankEnd.blockOperator Kmat := by
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    funext x
    rw [FiniteRankEnd.blockOperator_apply]
    rfl
  rw [hblock, FiniteRankEnd.trace_blockOperator, ← _root_.map_sum]
  apply congrArg FiniteRankEnd.trace
  apply Subtype.ext
  -- The diagonal sum.
  have hdiag : (∑ x : L.Cosets, c • kernelTest σ B μU L (L.rep x) (L.rep x)) =
      Hecke.TestFunction.pullback (leviContinuousAut σ B).toHomeomorph ψ := by
    apply Subtype.ext
    funext m
    change (↑(∑ x : L.Cosets, c • kernelTest σ B μU L (L.rep x) (L.rep x)) :
      B.Levi E → ℂ) m = ψ (leviAut σ B m)
    rw [Submodule.coe_sum, Finset.sum_apply, hψ]
    rw [← sum_kernelValue_diag σ B μU μK L m]
    rfl
  rw [Submodule.coe_sum]
  calc (∑ x : L.Cosets, (Kmat x x).val) =
        ∑ x : L.Cosets, (leviTensorIntertwiner σ B A).toLinearMap ∘ₗ
          Hecke.integratedAction μM (B.blockTensor P) hτ.1
            (c • kernelTest σ B μU L (L.rep x) (L.rep x)) := by
          apply Finset.sum_congr rfl
          intro x _
          simp only [Kmat, Submodule.coe_smul, kernelOperator, map_smul, LinearMap.comp_smul]
    _ = (leviTensorIntertwiner σ B A).toLinearMap ∘ₗ
          Hecke.integratedAction μM (B.blockTensor P) hτ.1
            (∑ x : L.Cosets, c • kernelTest σ B μU L (L.rep x) (L.rep x)) := by
          rw [_root_.map_sum]
          apply LinearMap.ext
          intro v
          simp only [LinearMap.comp_apply, LinearMap.sum_apply, _root_.map_sum]
    _ = _ := by
          rw [hdiag, leviTensorIntertwiner_comp_integratedAction σ B hP A μM ψ]
          rfl

end Assembly

/-- **Twisted van Dijk formula** (Henniart–Lemaire 2011, II.4.5 (2)). -/
theorem twistedVanDijk : TwistedVanDijkStatement.{u, v, uW} := by
  intro F _ _ E _ _ _ _ _ _ σ n B W _ _ P hP A
  let _ : MeasurableSpace (GeneralLinear n E) := borel _
  have _ : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let _ : MeasurableSpace (B.Levi E) := borel _
  have _ : BorelSpace (B.Levi E) := ⟨rfl⟩
  intro μG _ μM _ μU _ μK _ _ hG hM hU φ ψ hψ
  exact twistedDistribution_inducedSigmaIntertwiner σ B hP A μM μG μU μK hG hM hU φ ψ hψ

end Langlands.BaseChange.TwistedVanDijk
