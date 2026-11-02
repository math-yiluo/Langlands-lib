import Langlands.Algebra.NonUnitalSeparationStatements
import Langlands.Algebra.LeftShiftSimpleQuotientProof
import Langlands.Algebra.NonUnitalSimplicityProof

/-!
# Renard B.III: original additive simplicity of the actual separating quotient

The canonical quotient action agrees with the reconstruction of its original
restriction. The separating class of `1` forces that restriction to be nonzero,
so the published simplicity restriction theorem applies to the actual quotient.
-/

set_option autoImplicit false

universe uA

namespace Langlands.Renard

open Langlands.Algebra

variable (A : Type uA) [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

/-- Reconstructing the specified original restriction recovers the canonical
module structure on this same actual quotient. -/
theorem unitizationQuotient_module_eq
    (I : Submodule (Unitization ℂ A) (Unitization ℂ A)) :
    CompatibleUnitization.module
        (Unitization.lift.symm (_root_.Algebra.lsmul ℂ ℂ (Unitization ℂ A ⧸ I))) =
      (inferInstance : Module (Unitization ℂ A) (Unitization ℂ A ⧸ I)) := by
  symm
  exact CompatibleUnitization.module_unique_of_isScalarTower _ inferInstance
    inferInstance (fun _ _ => rfl)

/-- The actual unitization quotient separates the original element, and its
specified original action is simple for every stable additive subgroup. -/
theorem nonUnitalLeftShiftSimpleQuotient :
    NonUnitalLeftShiftSimpleQuotientStatement A := by
  intro a z hz hleft
  obtain ⟨I, hI, hspan, hsimple, hsep⟩ :=
    leftShiftSimpleQuotient (Unitization ℂ A) (Unitization.inr a) z hz hleft
  let ρ : A →ₙₐ[ℂ] Module.End ℂ (Unitization ℂ A ⧸ I) :=
    Unitization.lift.symm (_root_.Algebra.lsmul ℂ ℂ (Unitization ℂ A ⧸ I))
  have hρ : ρ ≠ 0 := by
    intro hzero
    apply hsep
    change ρ a (I.mkQ 1) = 0
    rw [hzero, NonUnitalAlgHom.zero_apply, LinearMap.zero_apply]
  have hs : letI := CompatibleUnitization.module ρ
      IsSimpleModule (Unitization ℂ A) (Unitization ℂ A ⧸ I) := by
    rw [unitizationQuotient_module_eq A I]
    exact hsimple
  obtain ⟨hnt, hadd⟩ := CompatibleUnitization.simpleUnitizationRestriction ρ hρ hs
  exact ⟨I, hI, hspan, hsimple, hnt, hadd, hsep⟩

end Langlands.Renard
