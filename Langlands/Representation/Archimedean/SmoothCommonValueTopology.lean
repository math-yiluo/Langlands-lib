import Langlands.Representation.Archimedean.SmoothDerivativeOpenMapping

/-! # The word topology on a common space of smooth Banach vectors -/

noncomputable section

open Set Topology
open scoped ContDiff Manifold Uniformity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

universe uA uE

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] (R S : Aˣ →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, A)
local notation:max "D" R:max => DerivativeSmoothVectors I R
local notation:max "ε" R:max => derivativeCLM I R []

/-- When two jointly continuous actions on the same Banach space have the same
smooth subspace, the value-preserving identification is a continuous linear
equivalence for their genuine word topologies. -/
def SmoothCommonValueTopologyStatement : Prop :=
  IsContinuousRepresentation R → IsContinuousRepresentation S →
    smoothVectors I R = smoothVectors I S →
    ∃ e : D R ≃L[ℂ] D S, ∀ x, ε S (e x) = ε R x

set_option maxHeartbeats 600000 in
theorem smoothCommonValueTopology : SmoothCommonValueTopologyStatement R S := by
  intro hR hS h
  let e₀ : smoothVectors I R ≃ₗ[ℂ] smoothVectors I S :=
    { toFun := fun x => ⟨x.val, h ▸ x.prop⟩
      invFun := fun y => ⟨y.val, h.symm ▸ y.prop⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  let e : D R ≃ₗ[ℂ] D S := (toSmooth I R).trans (e₀.trans (toSmooth I S).symm)
  have he (x : D R) : ε S (e x) = ε R x := by
    change ((toSmooth I S) ((toSmooth I S).symm (e₀ ((toSmooth I R) x)))).val =
      ((toSmooth I R) x).val
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hεS : Function.Injective (ε S) :=
    fun _ _ hxy => (toSmooth I S).injective (Subtype.ext hxy)
  let F := ((ε R).comp (ContinuousLinearMap.fst ℂ (D R) (D S))) -
    ((ε S).comp (ContinuousLinearMap.snd ℂ (D R) (D S)))
  let W := F.toLinearMap.ker
  let j : W →L[ℂ] (D R × D S) := ⟨W.subtype, continuous_subtype_val⟩
  let p := (ContinuousLinearMap.fst ℂ (D R) (D S)).comp j
  let q := (ContinuousLinearMap.snd ℂ (D R) (D S)).comp j
  have hW (x : D R) (y : D S) : (x, y) ∈ W ↔ ε R x = ε S y := by
    change ε R x - ε S y = 0 ↔ _
    exact sub_eq_zero
  have hp : Function.Surjective p := fun x => ⟨⟨(x, e x), (hW _ _).mpr (he x).symm⟩, rfl⟩
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨⟨(x, e x), (hW _ _).mpr (he x).symm⟩, rfl⟩
  have hE (w : W) : e (p w) = q w :=
    hεS ((he (p w)).trans ((hW _ _).mp w.prop))
  let : TopologicalSpace.MetrizableSpace (D R) := metrizableSpace_of_finiteDimensional I R
  let : TopologicalSpace.MetrizableSpace (D S) := metrizableSpace_of_finiteDimensional I S
  let : CompleteSpace (D R) := completeSpace_of_isContinuousRepresentation_units R hR
  let : CompleteSpace (D S) := completeSpace_of_isContinuousRepresentation_units S hS
  let : IsUniformAddGroup W := W.toAddSubgroup.isUniformAddGroup
  let : ContinuousSMul ℝ W := inferInstanceAs (ContinuousSMul ℝ (W.restrictScalars ℝ))
  let : LocallyConvexSpace ℝ W := inferInstanceAs (LocallyConvexSpace ℝ (W.restrictScalars ℝ))
  let : CompleteSpace W := F.isClosed_ker.completeSpace_coe
  let : (𝓤 (D R)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  let : (𝓤 (D S)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  let : BaireSpace (D R) := inferInstance
  let : BaireSpace (D S) := inferInstance
  let : FirstCountableTopology W :=
    (show IsInducing (Subtype.val : W → D R × D S) from IsInducing.subtypeVal).firstCountableTopology
  have hop : IsOpenMap p := Langlands.Analysis.frechetOpenMapping _ _ (p.restrictScalars ℝ) hp
  have hoq : IsOpenMap q := Langlands.Analysis.frechetOpenMapping _ _ (q.restrictScalars ℝ) hq
  refine ⟨{ toLinearEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }, he⟩
  · apply (hop.isQuotientMap p.continuous hp).continuous_iff.mpr
    exact q.continuous.congr (fun w => (hE w).symm)
  · apply (hoq.isQuotientMap q.continuous hq).continuous_iff.mpr
    exact p.continuous.congr (fun w => (e.symm_apply_eq.mpr (hE w).symm).symm)

end Langlands.Archimedean.DerivativeSmoothVectors
