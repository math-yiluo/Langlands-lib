import Langlands.Algebra.RenardNilpotentFiltrationVanishingStatement
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! Dimension-indexed vanishing of Renard's actual ideal-power filtration. -/

namespace Langlands.Renard

open scoped IsMulCommutative

universe u

namespace NilpotentFiltration

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {l : ℕ} (a : Fin l → Module.End ℂ V)

/-- A level of the actual filtration can stabilize only at zero. -/
theorem idealPowerSubspace_eq_bot_of_eq_succ
    (hcomm : ∀ i j, Commute (a i) (a j))
    (hnil : ∀ i, IsNilpotent (a i)) (n : ℕ)
    (heq : idealPowerSubspace a (n + 1) = idealPowerSubspace a n) :
    idealPowerSubspace a n = ⊥ := by
  let : IsMulCommutative (generatedAlgebra a) := generatedAlgebra_isMulCommutative a hcomm
  have hrad : generatorIdeal a ≤ (⊥ : Ideal (generatedAlgebra a)).radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hgen : IsNilpotent (generator a i) :=
      (IsNilpotent.map_iff (f := (generatedAlgebra a).val) Subtype.val_injective).mp (hnil i)
    obtain ⟨k, hk⟩ := hgen
    exact ⟨k, hk⟩
  have hfg : (idealPowerModule a n).FG := by
    apply Submodule.FG.of_restrictScalars ℂ
    exact (Submodule.fg_iff_finiteDimensional _).mpr inferInstance
  have hle : idealPowerModule a n ≤ generatorIdeal a • idealPowerModule a n := by
    rw [← idealPowerModule_succ]
    intro v hv
    change v ∈ idealPowerSubspace a (n + 1)
    rw [heq]
    exact hv
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (generatorIdeal a) (idealPowerModule a n) hfg hle
    (hrad.trans Ideal.radical_le_jacobson)
  simp only [idealPowerSubspace, hbot, Submodule.restrictScalars_bot]

/-- Each actual filtration level has dimension at most the remaining ambient dimension. -/
theorem idealPowerSubspace_finrank_le
    (hcomm : ∀ i j, Commute (a i) (a j))
    (hnil : ∀ i, IsNilpotent (a i)) (n : ℕ) :
    Module.finrank ℂ (idealPowerSubspace a n) ≤ Module.finrank ℂ V - n := by
  induction n with
  | zero =>
    rw [idealPowerSubspace_zero, finrank_top, Nat.sub_zero]
  | succ n ih =>
    by_cases hz : idealPowerSubspace a (n + 1) = ⊥
    · rw [hz, finrank_bot]
      exact Nat.zero_le _
    have hle : idealPowerSubspace a (n + 1) ≤ idealPowerSubspace a n :=
      idealPowerSubspace_antitone a (Nat.le_succ n)
    have hlt : Module.finrank ℂ (idealPowerSubspace a (n + 1)) <
        Module.finrank ℂ (idealPowerSubspace a n) := by
      by_contra h
      have heq := Submodule.eq_of_le_of_finrank_le hle (Nat.le_of_not_gt h)
      exact hz (heq.trans (idealPowerSubspace_eq_bot_of_eq_succ a hcomm hnil n heq))
    omega

end NilpotentFiltration

/-- Renard C.I: the actual ideal-power filtration vanishes at the ambient dimension. -/
theorem nilpotentFiltrationVanishing : NilpotentFiltrationVanishingStatement.{u} := by
  intro V _ _ _ l a hcomm hnil
  apply Submodule.finrank_eq_zero.mp
  exact Nat.eq_zero_of_le_zero (by
    simpa using NilpotentFiltration.idealPowerSubspace_finrank_le a hcomm hnil
      (Module.finrank ℂ V))

end Langlands.Renard
