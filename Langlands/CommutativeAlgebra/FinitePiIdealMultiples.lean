import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Operations

/-! # Ideal multiples of finite coordinate modules -/

universe u v

namespace Langlands.CommutativeAlgebra

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]

/-- The submodule of vectors whose coordinates all belong to an ideal. -/
def coordinateIdealSubmodule (I : Ideal R) : Submodule R (ι → R) :=
  Submodule.pi Set.univ (fun _ ↦ I)

/-- An element of a finite coordinate module belongs to the ideal multiple
exactly when all of its coordinates belong to the ideal. -/
theorem mem_ideal_smul_top_pi_iff (I : Ideal R) (x : ι → R) :
    x ∈ I • (⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ I := by
  classical
  constructor
  · intro hx i
    have hle : I • (⊤ : Submodule R (ι → R)) ≤
        (I : Submodule R R).comap (LinearMap.proj i) := by
      apply Submodule.smul_le.mpr
      intro r hr y _
      change r * y i ∈ I
      exact I.mul_mem_right _ hr
    exact hle hx
  · intro hx
    rw [← LinearMap.sum_single_apply (fun _ : ι ↦ R) x]
    apply Submodule.sum_mem
    intro i _
    have h := Submodule.smul_mem_smul (hx i)
      (show Pi.single i (1 : R) ∈ (⊤ : Submodule R (ι → R)) from trivial)
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using h

theorem ideal_smul_top_eq_coordinateIdealSubmodule (I : Ideal R) :
    I • (⊤ : Submodule R (ι → R)) = coordinateIdealSubmodule I := by
  ext x
  simpa [coordinateIdealSubmodule, Submodule.mem_pi] using
    (mem_ideal_smul_top_pi_iff I x)

/-- The square-ideal multiple is detected coordinatewise as well. -/
theorem mem_ideal_smul_smul_top_pi_iff (I : Ideal R) (x : ι → R) :
    x ∈ I • (I • (⊤ : Submodule R (ι → R))) ↔ ∀ i, x i ∈ I ^ 2 := by
  rw [← Submodule.mul_smul, ← pow_two]
  exact mem_ideal_smul_top_pi_iff _ _

end Langlands.CommutativeAlgebra
