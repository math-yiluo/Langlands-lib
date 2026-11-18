import Langlands.Algebra.RosenlichtTensorUnitsStatement
import Langlands.Algebra.RosenlichtBoundedInversePairsStatement
import Langlands.Algebra.RosenlichtSpecialization

/-! Reduction of Rosenlicht tensor units to bounded inverse-pair finiteness. -/

universe u v w

open scoped TensorProduct

noncomputable section

namespace Langlands.Algebra.Rosenlicht

/-- Bounded inverse-pair finiteness supplies the exact tensor-unit statement. -/
theorem tensorUnits_of_boundedInversePairs
    (h : Langlands.Algebra.RosenlichtBoundedInversePairsStatement.{u,w}) :
    Langlands.Algebra.RosenlichtTensorUnitsStatement.{u,v,w} := by
  intro k _ _ A _ _ _ _ B _ _ _ _ z
  obtain ⟨epsilon⟩ := exists_point (k := k) (A := B)
  let E : (A ⊗[k] B)ˣ →* Aˣ := Units.map (evaluateRight epsilon).toMonoidHom
  let L : Aˣ →* (A ⊗[k] B)ˣ :=
    Units.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toMonoidHom
  have hEL (a : Aˣ) : E (L a) = a := by
    apply Units.ext
    simp [E, L]
  let a : Aˣ := E z
  let z0 : (A ⊗[k] B)ˣ := (L a)⁻¹ * z
  have hE : E z0 = 1 := by
    simp only [z0, map_mul, map_inv, hEL, a, inv_mul_cancel]
  have hnorm : evaluateRight epsilon (z0 : A ⊗[k] B) = 1 := by
    exact congrArg (fun c : Aˣ => (c : A)) hE
  have hnormInv : evaluateRight epsilon ((z0⁻¹ : (A ⊗[k] B)ˣ) : A ⊗[k] B) = 1 := by
    change ((E (z0⁻¹) : Aˣ) : A) = 1
    rw [map_inv, hE, inv_one, Units.val_one]
  obtain ⟨V, hV, htV⟩ := exists_finite_specialization_space (z0 : A ⊗[k] B)
  obtain ⟨W, hW, htW⟩ :=
    exists_finite_specialization_space ((z0⁻¹ : (A ⊗[k] B)ˣ) : A ⊗[k] B)
  let : Module.Finite k V := Module.Finite.of_fg hV
  let : Module.Finite k W := Module.Finite.of_fg hW
  have hfPairs := h k B epsilon V W
  have hpair (x : A →ₐ[k] k) :
      (specialize x (z0 : A ⊗[k] B),
        specialize x ((z0⁻¹ : (A ⊗[k] B)ˣ) : A ⊗[k] B)) ∈
      {p : B × B | p.1 ∈ V ∧ p.2 ∈ W ∧ p.1 * p.2 = 1 ∧
        epsilon p.1 = 1 ∧ epsilon p.2 = 1} := by
    refine ⟨htV x, htW x, ?_, ?_, ?_⟩
    · rw [← map_mul]
      simp
    · rw [specialize_evaluateRight, hnorm, map_one]
    · rw [specialize_evaluateRight, hnormInv, map_one]
  have hf : (Set.range (fun x : A →ₐ[k] k => specialize x (z0 : A ⊗[k] B))).Finite := by
    apply (hfPairs.image Prod.fst).subset
    rintro b ⟨x, rfl⟩
    exact ⟨_, hpair x, rfl⟩
  obtain ⟨b, hb⟩ := constant_of_finite_specializations (z0 : A ⊗[k] B) hf
  obtain ⟨x0⟩ := exists_point (k := k) (A := A)
  let b0 : Bˣ := Units.map (specialize x0).toMonoidHom z0
  have hb0 : (b0 : B) = b := by
    change specialize x0 (z0 : A ⊗[k] B) = b
    rw [hb]
    simp
  refine ⟨a, b0, ?_⟩
  have hz : (z : A ⊗[k] B) = (L a : A ⊗[k] B) * (z0 : A ⊗[k] B) := by
    have hu : z = L a * z0 := by simp [z0]
    exact congrArg (fun c : (A ⊗[k] B)ˣ => (c : A ⊗[k] B)) hu
  rw [hz, hb, ← hb0]
  simp [L]

end Langlands.Algebra.Rosenlicht
