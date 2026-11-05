import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Finite coefficient models of tensor units -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.AffineCharacterFiniteGalois

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
variable (A : Type u) [CommRing A] [Algebra k A]

/-- The coefficient embedding from a finite Galois intermediate field. -/
def tensorEmbed (E : FiniteGaloisIntermediateField k K) :
    E ⊗[k] A →ₐ[k] K ⊗[k] A :=
  Algebra.TensorProduct.map E.toIntermediateField.val (AlgHom.id k A)

omit [IsGalois k K] in
/-- Increasing the coefficient field commutes with embedding in the ambient tensor algebra. -/
theorem tensorEmbed_inclusion {E F : FiniteGaloisIntermediateField k K}
    (h : E ≤ F) (x : E ⊗[k] A) :
    tensorEmbed A F
      (Algebra.TensorProduct.map (IntermediateField.inclusion h) (AlgHom.id k A) x) =
    tensorEmbed A E x := by
  change ((tensorEmbed A F).comp
    (Algebra.TensorProduct.map (IntermediateField.inclusion h) (AlgHom.id k A))) x = _
  rw [tensorEmbed, ← Algebra.TensorProduct.map_comp]
  rfl

/-- Every tensor uses only finitely many extension coefficients. -/
theorem exists_tensorEmbed_eq (x : K ⊗[k] A) :
    ∃ E : FiniteGaloisIntermediateField k K, ∃ y : E ⊗[k] A,
      tensorEmbed A E y = x := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul c a =>
      let E := FiniteGaloisIntermediateField.adjoin k ({c} : Set K)
      have hc : c ∈ E.toIntermediateField :=
        FiniteGaloisIntermediateField.subset_adjoin k {c} (Set.mem_singleton c)
      exact ⟨E, (⟨c, hc⟩ : E) ⊗ₜ[k] a, rfl⟩
  | add x y hx hy =>
      obtain ⟨E, xE, hx⟩ := hx
      obtain ⟨F, yF, hy⟩ := hy
      let N := E ⊔ F
      refine ⟨N,
        Algebra.TensorProduct.map (IntermediateField.inclusion (show E ≤ N from le_sup_left))
          (AlgHom.id k A) xE +
        Algebra.TensorProduct.map (IntermediateField.inclusion (show F ≤ N from le_sup_right))
          (AlgHom.id k A) yF, ?_⟩
      rw [map_add, tensorEmbed_inclusion, tensorEmbed_inclusion, hx, hy]

omit [IsGalois k K] in
/-- Tensoring the inclusion of a coefficient field stays injective. -/
theorem tensorEmbed_injective (E : FiniteGaloisIntermediateField k K) :
    Function.Injective (tensorEmbed A E) :=
  TensorProduct.map_injective_of_flat_flat E.toIntermediateField.val.toLinearMap
    (LinearMap.id : A →ₗ[k] A) E.toIntermediateField.val.injective Function.injective_id

/-- A tensor unit and its inverse descend to a common finite Galois coefficient field. -/
theorem exists_tensorEmbed_unit (x : (K ⊗[k] A)ˣ) :
    ∃ E : FiniteGaloisIntermediateField k K, ∃ y : (E ⊗[k] A)ˣ,
      Units.map (tensorEmbed A E).toMonoidHom y = x := by
  classical
  obtain ⟨E, a, ha⟩ := exists_tensorEmbed_eq A (x : K ⊗[k] A)
  obtain ⟨F, b, hb⟩ := exists_tensorEmbed_eq A (↑x⁻¹ : K ⊗[k] A)
  let N := E ⊔ F
  let aN := Algebra.TensorProduct.map
    (IntermediateField.inclusion (show E ≤ N from le_sup_left)) (AlgHom.id k A) a
  let bN := Algebra.TensorProduct.map
    (IntermediateField.inclusion (show F ≤ N from le_sup_right)) (AlgHom.id k A) b
  have haN : tensorEmbed A N aN = x := (tensorEmbed_inclusion A _ a).trans ha
  have hbN : tensorEmbed A N bN = ↑x⁻¹ := (tensorEmbed_inclusion A _ b).trans hb
  have hab : aN * bN = 1 := by
    apply tensorEmbed_injective A N
    calc
      tensorEmbed A N (aN * bN) =
        tensorEmbed A N aN * tensorEmbed A N bN := (tensorEmbed A N).map_mul' _ _
      _ = 1 := by rw [haN, hbN, Units.mul_inv]
      _ = tensorEmbed A N 1 := (tensorEmbed A N).map_one'.symm
  exact ⟨N, ⟨aN, bN, hab, (mul_comm bN aN).trans hab⟩, Units.ext haN⟩

end Langlands.GroupScheme.AffineCharacterFiniteGalois
