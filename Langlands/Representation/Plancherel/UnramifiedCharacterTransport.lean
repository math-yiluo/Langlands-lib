import Langlands.Representation.Plancherel.UnramifiedCharacters
import Mathlib.Topology.Algebra.Group.CompactOpen

/-! # Unramified characters under a multiplicative homeomorphism -/

noncomputable section

open scoped NNReal

namespace Langlands.Plancherel

universe uA uB uI

variable {A : Type uA} [Group A] [TopologicalSpace A]
variable {B : Type uB} [Group B] [TopologicalSpace B]
variable {I : Type uI}

private def transportCharacter (e : A ≃ₜ* B) (ν : I → (A →* ℝ≥0ˣ))
    (χ : unramifiedCharacters ν) :
    unramifiedCharacters (fun j => (ν j).comp e.symm.toMulEquiv.toMonoidHom) :=
  ⟨χ.val.comp (e.symm : B →ₜ* A), by
    intro b hb
    change χ.val (e.symm b) = 1
    apply χ.property
    exact (mem_commonNormKernel ν (e.symm b)).mpr
      ((mem_commonNormKernel _ b).mp hb)⟩

private def transportCharacterInverse (e : A ≃ₜ* B) (ν : I → (A →* ℝ≥0ˣ))
    (χ : unramifiedCharacters (fun j => (ν j).comp e.symm.toMulEquiv.toMonoidHom)) :
    unramifiedCharacters ν :=
  ⟨χ.val.comp (e : A →ₜ* B), by
    intro a ha
    change χ.val (e a) = 1
    apply χ.property
    apply (mem_commonNormKernel _ (e a)).mpr
    intro j
    change ν j (e.symm (e a)) = 1
    rw [e.symm_apply_apply]
    exact (mem_commonNormKernel ν a).mp ha j⟩

/-- Transport continuous unramified characters through an actual multiplicative
homeomorphism, retaining the entire indexed norm family. -/
def unramifiedCharactersHomeomorph (e : A ≃ₜ* B) (ν : I → (A →* ℝ≥0ˣ)) :
    unramifiedCharacters ν ≃ₜ*
      unramifiedCharacters (fun j => (ν j).comp e.symm.toMulEquiv.toMonoidHom) where
  toFun := transportCharacter e ν
  invFun := transportCharacterInverse e ν
  left_inv χ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro a
    change χ.val (e.symm (e a)) = χ.val a
    rw [e.symm_apply_apply]
  right_inv χ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro b
    change χ.val (e (e.symm b)) = χ.val b
    rw [e.apply_symm_apply]
  map_mul' χ η := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro b
    rfl
  continuous_toFun :=
    ((e.symm : B →ₜ* A).continuous_comp_left.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((e : A →ₜ* B).continuous_comp_left.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem unramifiedCharactersHomeomorph_apply (e : A ≃ₜ* B) (ν : I → (A →* ℝ≥0ˣ))
    (χ : unramifiedCharacters ν) (b : B) :
    (unramifiedCharactersHomeomorph e ν χ).val b = χ.val (e.symm b) := rfl

@[simp]
theorem unramifiedCharactersHomeomorph_symm_apply (e : A ≃ₜ* B) (ν : I → (A →* ℝ≥0ˣ))
    (χ : unramifiedCharacters (fun j => (ν j).comp e.symm.toMulEquiv.toMonoidHom)) (a : A) :
    ((unramifiedCharactersHomeomorph e ν).symm χ).val a = χ.val (e a) := rfl

end Langlands.Plancherel
