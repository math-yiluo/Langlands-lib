import Langlands.Representation.RankinSelberg.CharacterChange
import Langlands.Representation.RankinSelberg.ModelMinusOneScalar

/-! Algebra for the fixed-character equal-rank exchange. -/

noncomputable section

namespace Langlands.RankinSelberg

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV

section Matrix

variable {F : Type uF} [Field F]

theorem characterChangeElement_neg_one_inv (n : ℕ) :
    (characterChangeElement (-1 : Fˣ) n)⁻¹ = characterChangeElement (-1 : Fˣ) n := by
  rw [characterChangeElement_inv]
  simp

theorem inverseTranspose_characterChangeElement_neg_one (n : ℕ) :
    inverseTranspose (n + 1) F (characterChangeElement (-1 : Fˣ) n) =
      characterChangeElement (-1 : Fˣ) n := by
  apply Units.ext
  simp [inverseTranspose_coe, characterChangeElement_neg_one_inv,
    characterChangeElement_val]

private theorem minusOne_pow_mul_entry (n k : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) (i j : Fin (n + 1)) :
    (((-1 : Langlands.GeneralLinear (n + 1) F) ^ k * g).val i j) =
      (-1 : F) ^ k * g.val i j := by
  induction k with
  | zero => simp
  | succ k ih =>
    simpa only [pow_succ', mul_assoc, Units.val_mul, Units.val_neg, Units.val_one,
      Matrix.neg_mul, Matrix.one_mul, Matrix.neg_apply, neg_one_mul, neg_mul, one_mul] using
      congrArg Neg.neg ih

theorem characterChangeElement_neg_one_mul_weylLong (n : ℕ) :
    characterChangeElement (-1 : Fˣ) n * weylLong (n + 1) F =
      (-1 : Langlands.GeneralLinear (n + 1) F) ^ n *
        (weylLong (n + 1) F * characterChangeElement (-1 : Fˣ) n) := by
  apply Units.ext
  ext i j
  rw [mul_weylLong_entry, minusOne_pow_mul_entry, weylLong_mul_entry]
  simp only [characterChangeElement_val, Matrix.diagonal_apply, Fin.rev_eq_iff]
  split_ifs with hij
  · have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    have hsum : (n - i.val) + i.val = n := Nat.sub_add_cancel hi
    have hrev : n - i.rev.val = i.val := by
      simp only [Fin.val_rev]
      omega
    rw [hrev]
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    have hpow : (-1 : F) ^ n = (-1 : F) ^ (n - i.val) * (-1 : F) ^ i.val := by
      rw [← pow_add, hsum]
    have hsq : (-1 : F) ^ i.val * (-1 : F) ^ i.val = 1 := by
      rw [← mul_pow]
      simp
    rw [hpow, mul_assoc, hsq, mul_one]
  · simp

theorem characterChangeModulus_neg_one (abv : AbsoluteValue F ℝ) (n : ℕ) :
    characterChangeModulus abv (-1 : Fˣ) n = 1 := by
  apply Subtype.ext
  simp [characterChangeModulus]

theorem determinantWeight_characterChangeElement_neg_one
    (abv : AbsoluteValue F ℝ) (n : ℕ) (s : ℂ) :
    determinantWeight abv (characterChangeElement (-1 : Fˣ) n) s = 1 := by
  simp [determinantWeight, characterChangeElement_val, Matrix.det_diagonal, map_prod]

end Matrix

section ModelScalar

variable {F : Type uF} [Field F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {θ : upperUnipotent (n + 1) F →* ℂˣ}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {ℓ : functionals (upperUnipotent (n + 1) F) θ π} {ζ : ℂˣ}

theorem HasModelMinusOneScalar.pow_apply (hζ : HasModelMinusOneScalar π ℓ ζ)
    (k : ℕ) (f : (coefficientModel π ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (n + 1) F) :
    f.val.val ((-1) ^ k * g) = (ζ : ℂ) ^ k * f.val.val g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, hζ, ih, pow_succ', mul_assoc]

theorem HasModelMinusOneScalar.sq_eq_one (hζ : HasModelMinusOneScalar π ℓ ζ)
    (hℓ : ℓ.val ≠ 0) : ζ ^ 2 = 1 := by
  obtain ⟨v, hv⟩ : ∃ v, ℓ.val v ≠ 0 := by
    by_contra! hzero
    apply hℓ
    ext v
    exact hzero v
  have h := hζ.pow_apply 2 (modelMap π ℓ v) 1
  have hzero : ((-1 : Langlands.GeneralLinear (n + 1) F) ^ 2) = 1 := by
    simp [pow_two]
  rw [hzero, one_mul] at h
  have hv' : (modelMap π ℓ v).val.val 1 ≠ 0 := by
    change ℓ.val (π 1 v) ≠ 0
    simpa only [map_one, Module.End.one_apply] using hv
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
    (mul_right_cancel₀ hv' (h.symm.trans (one_mul _).symm))

/-- Translating a dual coefficient by the diagonal introduces precisely the
`n`-th power of its actual minus-one scalar. -/
theorem HasModelMinusOneScalar.negOne_dual_apply (hζ : HasModelMinusOneScalar π ℓ ζ)
    (f : (coefficientModel π ℓ).toSubmodule) (g : Langlands.GeneralLinear (n + 1) F) :
    f.val.val (characterChangeElement (-1) n *
        (weylLong (n + 1) F * inverseTranspose (n + 1) F g)) =
      (ζ : ℂ) ^ n * f.val.val (weylLong (n + 1) F *
        inverseTranspose (n + 1) F (characterChangeElement (-1) n * g)) := by
  have hm : characterChangeElement (-1 : Fˣ) n *
        (weylLong (n + 1) F * inverseTranspose (n + 1) F g) =
      (-1 : Langlands.GeneralLinear (n + 1) F) ^ n *
        (weylLong (n + 1) F * inverseTranspose (n + 1) F
          (characterChangeElement (-1) n * g)) := by
    rw [map_mul, inverseTranspose_characterChangeElement_neg_one,
      ← mul_assoc, characterChangeElement_neg_one_mul_weylLong]
    simp only [mul_assoc]
  rw [hm, hζ.pow_apply]

end ModelScalar

end Langlands.RankinSelberg
