import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.Tactic

/-! # Reducedness from the absence of double roots -/

noncomputable section

namespace RootPairing

variable {J M N : Type*} [AddCommGroup M] [Module ℝ M]
  [AddCommGroup N] [Module ℝ N] [Finite J]

/-- A finite crystallographic real root pairing is reduced if no root is twice another. -/
theorem isReduced_of_no_double (P : RootPairing J ℝ M N) [P.IsCrystallographic]
    (hdouble : ∀ a b, P.root b ≠ (2 : ℝ) • P.root a) : P.IsReduced := by
  have hnegdouble (a b : J) : P.root b ≠ (-2 : ℝ) • P.root a := by
    intro h
    apply hdouble (P.reflectionPerm a a) b
    simpa only [P.root_reflectionPerm, P.reflection_apply_self, smul_neg, neg_smul] using h
  constructor
  intro a b hdep
  have hprod : P.pairingIn ℤ a b * P.pairingIn ℤ b a = 4 :=
    (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).mpr hdep
  have hbne : P.pairingIn ℤ b a ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    norm_num at hprod
  have habs : |P.pairingIn ℤ a b| * |P.pairingIn ℤ b a| = 4 := by
    rw [← abs_mul, hprod]
    norm_num
  have hbpos : 1 ≤ |P.pairingIn ℤ b a| := by
    have := abs_pos.mpr hbne
    omega
  have hbound : -4 ≤ P.pairingIn ℤ a b ∧ P.pairingIn ℤ a b ≤ 4 := by
    have hle : |P.pairingIn ℤ a b| ≤ 4 := by
      nlinarith [abs_nonneg (P.pairingIn ℤ a b)]
    constructor <;>
      linarith [le_abs_self (P.pairingIn ℤ a b), neg_le_abs (P.pairingIn ℤ a b)]
  obtain ⟨hlo, hhi⟩ := hbound
  interval_cases hp : P.pairingIn ℤ a b
  · have hq : P.pairingIn ℤ b a = -1 := by omega
    exact False.elim (hnegdouble b a
      ((P.pairingIn_neg_one_neg_four_iff ℤ b a).mp ⟨hq, hp⟩))
  · omega
  · have hq : P.pairingIn ℤ b a = -2 := by omega
    exact Or.inr ((P.pairingIn_neg_two_neg_two_iff ℤ a b).mp ⟨hp, hq⟩)
  · have hq : P.pairingIn ℤ b a = -4 := by omega
    exact False.elim (hnegdouble a b
      ((P.pairingIn_neg_one_neg_four_iff ℤ a b).mp ⟨hp, hq⟩))
  · omega
  · have hq : P.pairingIn ℤ b a = 4 := by omega
    exact False.elim (hdouble a b
      ((P.pairingIn_one_four_iff ℤ a b).mp ⟨hp, hq⟩))
  · have hq : P.pairingIn ℤ b a = 2 := by omega
    exact Or.inl (congrArg P.root ((P.pairingIn_two_two_iff ℤ a b).mp ⟨hp, hq⟩))
  · omega
  · have hq : P.pairingIn ℤ b a = 1 := by omega
    exact False.elim (hdouble b a
      ((P.pairingIn_one_four_iff ℤ b a).mp ⟨hq, hp⟩))

end RootPairing
