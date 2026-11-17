import Langlands.Global.RankinSelberg.RectangularCorrectionDenominator

/-! # Finite denominators of actual diagonal corrections and leading roots -/

noncomputable section
universe u
open NumberField
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open PrimitiveAdelicHeight Langlands.GeneralLinear.RectangularIwasawa

variable (F : Type u) [Field F] [NumberField F]

/-- The finite-idele tuple obtained from a full idelic diagonal. -/
def finiteDiagonalIdeles {n : ℕ} (c : Fin n → Ideles F) : Fin n → FiniteIdeles F :=
  fun i => Units.map (RingHom.snd (InfiniteAdeles F) (FiniteAdeles F)).toMonoidHom (c i)

/-- A scalar denominator for the finite rectangle also clears the
Iwasawa correction and its inverse at every finite place simultaneously. -/
theorem finite_diagonal_correction_integral_multiple
    {a d : ℕ} (x : Matrix (Fin d) (Fin a) (Adeles F))
    (U K : AdelicGL F (a + d + 1)) (c : Fin (a + d + 1) → Ideles F)
    (hU : IsUnitriangular U.val) (hK : K ∈ standardCompact F (a + d + 1))
    (hfac : GeneralLinear.lowerBlockLocalization 1 1 x 1 = U * diagonalGL c * K)
    (s : FiniteAdeles F) (hs : s ∈ integralFiniteAdeles F)
    (hx : ∀ i j, s * rectangleFiniteCoordinates F d a x i j ∈ integralFiniteAdeles F) :
    HasIntegralMultipleUnitTuple (integralFiniteAdeles F) s (finiteDiagonalIdeles F c) := by
  let f : Adeles F →+* FiniteAdeles F := RingHom.snd _ _
  have hk := ((mem_standardCompact_iff F _ K).mp hK).2
  change (∀ i j, (Matrix.GeneralLinearGroup.map f K) i j ∈ integralFiniteAdeles F) ∧
    (∀ i j, (Matrix.GeneralLinearGroup.map f K)⁻¹ i j ∈ integralFiniteAdeles F) at hk
  have hlocal :
      GeneralLinear.lowerBlockPair 1 ((extendRectangle 1 x).map f) 1 =
        Matrix.GeneralLinearGroup.map f U *
          diagonalGL (finiteDiagonalIdeles F c) * Matrix.GeneralLinearGroup.map f K := by
    have hh := congrArg (Matrix.GeneralLinearGroup.map f) hfac
    rw [lowerBlockLocalization_one_eq_pair,
      map_lowerBlockPair_one f 1 (extendRectangle 1 x),
      map_mul, map_mul, map_diagonalGL_units, map_one] at hh
    exact hh
  apply integral_multiple_diagonal_correction (integralFiniteAdeles F) s hs
    ((extendRectangle 1 x).map f) (Matrix.GeneralLinearGroup.map f U)
    (Matrix.GeneralLinearGroup.map f K) (finiteDiagonalIdeles F c)
    (hU.map f) hk.1 hk.2 hlocal
  intro i j
  induction i using Fin.addCases with
  | left i =>
    simp only [Matrix.map_apply, extendRectangle, Fin.append_left]
    exact hx i j
  | right i =>
    simp only [Matrix.map_apply, extendRectangle, Fin.append_right, Pi.zero_apply, map_zero,
      mul_zero]
    exact (integralFiniteAdeles F).zero_mem

/-- The recovered original block roots have denominator equal to the
actual-root denominator times the square of a correction denominator. -/
theorem leading_block_root_integral_multiple
    {t r : ℕ} (h : t < r) (b : Fin (t + 1) → Ideles F)
    (c : Fin (r + 1) → Ideles F) (q s : FiniteAdeles F)
    (hactual : ∀ k : Fin r,
      q * ((gaugeSimpleRootIdeles F r (rectangularCorrectedDiagonal F b c) k :
        Ideles F) : Adeles F).2 ∈ integralFiniteAdeles F)
    (hc : HasIntegralMultipleUnitTuple (integralFiniteAdeles F) s (finiteDiagonalIdeles F c))
    (i : Fin (t + 1)) :
    (q * s ^ 2) * (gaugeBlockRootIdeles F t b i : Adeles F).2 ∈ integralFiniteAdeles F := by
  let k := Fin.castLE (Nat.succ_le_of_lt h) i
  have hcorr := hc.div_mem k.succ k.castSucc
  change s ^ 2 * ((c k.succ / c k.castSucc : Ideles F) : Adeles F).2 ∈
    integralFiniteAdeles F at hcorr
  have he : (gaugeBlockRootIdeles F t b i : Adeles F).2 =
      (gaugeSimpleRootIdeles F r (rectangularCorrectedDiagonal F b c) k : Adeles F).2 *
        ((c k.succ / c k.castSucc : Ideles F) : Adeles F).2 := by
    rw [gaugeBlockRootIdeles_eq_corrected_mul_inverse F h b c i]
    simp only [gaugeSimpleRootIdeles, inv_div, Units.val_mul]
    rfl
  have hh := (integralFiniteAdeles F).mul_mem (hactual k) hcorr
  convert hh using 1
  rw [he]
  ring

end Langlands.Global.RankinSelbergGlobal
