import Langlands.Geometry.Analytic.CompletedTensorAlgebra
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Bounded universal extension of the actual completed tensor algebra -/

noncomputable section

universe u v w z

open scoped TensorProduct NNReal

namespace Langlands.Analytic.CompletedTensorAlgebra

variable {K : Type u} [NormedField K]
  {A : Type v} [NormedCommRing A] [NormedAlgebra K A]
  {B : Type w} [NormedCommRing B] [NormedAlgebra K B]
  {E : Type z} [NormedCommRing E] [NormedAlgebra K E] [IsUltrametricDist E]
  (α : BoundedAlgHom K A E) (β : BoundedAlgHom K B E)

/-- The algebraic tensor map is constructed from the two original maps. -/
def algebraicLift : Algebraic K A B →ₐ[K] E :=
  Algebra.TensorProduct.lift α.toAlgHom β.toAlgHom (fun _ _ => Commute.all _ _)

omit [IsUltrametricDist E] in
@[simp]
theorem algebraicLift_tmul (a : A) (b : B) :
    algebraicLift α β (a ⊗ₜ[K] b) = α a * β b := rfl

/-- The product of any two positive original bounds bounds the algebraic
tensor map for the actual infimum of finite-maximum representations. -/
theorem norm_algebraicLift_le (M N : ℝ) (hM : 0 < M) (hN : 0 < N)
    (hα : ∀ a : A, ‖α a‖ ≤ M * ‖a‖)
    (hβ : ∀ b : B, ‖β b‖ ≤ N * ‖b‖) (t : Algebraic K A B) :
    ‖algebraicLift α β t‖ ≤ (M * N) * ‖t‖ := by
  let m : ℝ≥0 := ⟨M, hM.le⟩
  let n : ℝ≥0 := ⟨N, hN.le⟩
  let t' : A ⊗[K] B := t
  have hn : ‖algebraicLift α β t‖₊ ≤
      (m * n) *
        UltrametricTensorSeminorm.seminormFun t' := by
    apply NNReal.le_mul_iInf
    intro r
    have hs : algebraicLift α β t = ∑ i, α (r.left i) * β (r.right i) := by
      calc
        _ = algebraicLift α β (∑ i, r.left i ⊗ₜ[K] r.right i) :=
          congrArg (algebraicLift α β) r.sum_eq.symm
        _ = _ := (map_sum (algebraicLift α β)
          (fun i => (r.left i ⊗ₜ[K] r.right i : Algebraic K A B)) Finset.univ).trans
            (Finset.sum_congr rfl fun i _ => algebraicLift_tmul α β (r.left i) (r.right i))
    have hbound : ‖algebraicLift α β t‖ ≤ (M * N) * (r.value : ℝ) := by
      rw [hs]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (mul_nonneg (mul_pos hM hN).le r.value.coe_nonneg)
      intro i _
      calc
        ‖α (r.left i) * β (r.right i)‖
            ≤ ‖α (r.left i)‖ * ‖β (r.right i)‖ := norm_mul_le _ _
        _ ≤ (M * ‖r.left i‖) * (N * ‖r.right i‖) :=
          mul_le_mul (hα _) (hβ _) (norm_nonneg _) (by positivity)
        _ = (M * N) * (‖r.left i‖ * ‖r.right i‖) := by ring
        _ ≤ (M * N) * (r.value : ℝ) := mul_le_mul_of_nonneg_left
          (by exact_mod_cast r.le_value i) (mul_pos hM hN).le
    exact_mod_cast hbound
  exact_mod_cast hn

theorem algebraicLift_continuous : Continuous (algebraicLift α β) := by
  obtain ⟨M, hM, hα⟩ := α.bounded
  obtain ⟨N, hN, hβ⟩ := β.bounded
  exact AddMonoidHomClass.continuous_of_bound (algebraicLift α β) (M * N)
    (norm_algebraicLift_le α β M N hM hN hα hβ)

variable [CompleteSpace E]

/-- The actual ring extension through the Hausdorff projective completion. -/
def extensionRingHom : Algebra K A B →+* E :=
  UniformSpace.Completion.extensionHom (algebraicLift α β).toRingHom
    (algebraicLift_continuous α β)

@[simp]
theorem extensionRingHom_toCompletion (t : Algebraic K A B) :
    extensionRingHom α β (toCompletion K A B t) = algebraicLift α β t :=
  UniformSpace.Completion.extensionHom_coe (algebraicLift α β).toRingHom
    (algebraicLift_continuous α β) t

theorem extensionRingHom_continuous : Continuous (extensionRingHom α β) :=
  UniformSpace.Completion.continuous_extension

/-- Closedness and density carry the same positive norm bound from the
algebraic tensor to every point of its actual completion. -/
theorem norm_extensionRingHom_le (M N : ℝ) (hM : 0 < M) (hN : 0 < N)
    (hα : ∀ a : A, ‖α a‖ ≤ M * ‖a‖)
    (hβ : ∀ b : B, ‖β b‖ ≤ N * ‖b‖) (t : Algebra K A B) :
    ‖extensionRingHom α β t‖ ≤ (M * N) * ‖t‖ := by
  induction t using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le (continuous_norm.comp (extensionRingHom_continuous α β))
      (by fun_prop)
  | ih t =>
    exact (congrArg norm (extensionRingHom_toCompletion α β t)).trans_le
      ((norm_algebraicLift_le α β M N hM hN hα hβ t).trans_eq
        (congrArg (fun r : ℝ => (M * N) * r)
          (UniformSpace.Completion.norm_coe t).symm))

/-- The genuine completed tensor lift retains the full bounded algebra
map, not only its action on spectrum points. -/
def lift : BoundedAlgHom K (Algebra K A B) E where
  toAlgHom := {
    __ := extensionRingHom α β
    commutes' c :=
      (extensionRingHom_toCompletion α β (algebraMap K (Algebraic K A B) c)).trans
        ((algebraicLift α β).commutes c) }
  bounded := by
    obtain ⟨M, hM, hα⟩ := α.bounded
    obtain ⟨N, hN, hβ⟩ := β.bounded
    exact ⟨M * N, mul_pos hM hN, norm_extensionRingHom_le α β M N hM hN hα hβ⟩

@[simp]
theorem lift_toCompletion (t : Algebraic K A B) :
    lift α β (toCompletion K A B t) = algebraicLift α β t :=
  extensionRingHom_toCompletion α β t

@[simp]
theorem lift_comp_leftMap :
    (lift α β).comp (leftMap K A B) = α := by
  apply BoundedAlgHom.ext
  intro a
  exact (lift_toCompletion α β (a ⊗ₜ[K] (1 : B))).trans
    (by simp only [algebraicLift_tmul, map_one, mul_one])

@[simp]
theorem lift_comp_rightMap :
    (lift α β).comp (rightMap K A B) = β := by
  apply BoundedAlgHom.ext
  intro b
  exact (lift_toCompletion α β ((1 : A) ⊗ₜ[K] b)).trans
    (by simp only [algebraicLift_tmul, map_one, one_mul])

omit [IsUltrametricDist E] [CompleteSpace E] in
/-- Equality of the two entire original leg composites determines a
bounded map on the completion, by algebraic tensor generation and density. -/
theorem hom_ext (f g : BoundedAlgHom K (Algebra K A B) E)
    (hl : f.comp (leftMap K A B) = g.comp (leftMap K A B))
    (hr : f.comp (rightMap K A B) = g.comp (rightMap K A B)) : f = g := by
  have halg : f.toAlgHom.comp (toCompletion K A B) =
      g.toAlgHom.comp (toCompletion K A B) := by
    apply Algebra.TensorProduct.ext
    · exact congrArg BoundedAlgHom.toAlgHom hl
    · exact congrArg BoundedAlgHom.toAlgHom hr
  have hfun : (f : Algebra K A B → E) = g :=
    (denseRange_toCompletion K A B).equalizer f.continuous g.continuous
      (funext fun t => congrArg
        (fun h : Algebraic K A B →ₐ[K] E => h t) halg)
  exact BoundedAlgHom.ext (congrFun hfun)

/-- The actual completed tensor algebra has the full bounded algebra
coproduct property for every complete ultrametric normed target algebra. -/
def boundedHomEquiv : BoundedAlgHom K (Algebra K A B) E ≃
    (BoundedAlgHom K A E × BoundedAlgHom K B E) where
  toFun f := ⟨f.comp (leftMap K A B), f.comp (rightMap K A B)⟩
  invFun p := lift p.1 p.2
  left_inv _f := hom_ext _ _ (lift_comp_leftMap _ _) (lift_comp_rightMap _ _)
  right_inv p := Prod.ext (lift_comp_leftMap p.1 p.2) (lift_comp_rightMap p.1 p.2)

end Langlands.Analytic.CompletedTensorAlgebra
