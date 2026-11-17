import Langlands.Global.RankinSelberg.RectangularIwasawaBounds
import Langlands.Global.AdelicGLSiegelShape
import Mathlib.Data.Fin.Tuple.Basic

/-! # The three-block rectangular chart and integral trailing roots -/

noncomputable section
universe u v
set_option autoImplicit false

namespace Langlands.GeneralLinear.RectangularIwasawa

variable {R : Type u} [CommRing R] {a d c : ℕ}

/-- Extend a rectangle by `c` zero rows. -/
def extendRectangle (c : ℕ) (x : Matrix (Fin d) (Fin a) R) :
    Matrix (Fin (d + c)) (Fin a) R :=
  fun i j => Fin.append (fun q => x q j) 0 i

private theorem assoc_first (i : Fin a) :
    (finCongr (Nat.add_assoc a d c)).symm (i.castAdd (d + c)) =
      lowerBlockFirst d c i := by
  apply Fin.ext
  rfl

private theorem assoc_middle (i : Fin d) :
    (finCongr (Nat.add_assoc a d c)).symm ((i.castAdd c).natAdd a) =
      lowerBlockMiddle a c i := by
  apply Fin.ext
  rfl

private theorem assoc_last (i : Fin c) :
    (finCongr (Nat.add_assoc a d c)).symm ((i.natAdd d).natAdd a) =
      lowerBlockLast a d i := by
  apply Fin.ext
  simp only [finCongr_symm, finCongr_apply, Fin.val_cast, Fin.val_natAdd,
    lowerBlockLast]
  omega

/-- Reassociating the three blocks identifies the chart with a two-block
chart whose rectangle has extra zero rows. -/
theorem lowerBlockLocalization_reindex
    (g : Langlands.GeneralLinear a R) (x : Matrix (Fin d) (Fin a) R) :
    reindex (finCongr (Nat.add_assoc a d c)) (lowerBlockLocalization c g x 1) =
      lowerBlockPair g (extendRectangle c x) 1 := by
  apply Units.ext
  ext i j
  change (lowerBlockLocalization c g x 1)
      ((finCongr (Nat.add_assoc a d c)).symm i)
      ((finCongr (Nat.add_assoc a d c)).symm j) =
    lowerBlockPair g (extendRectangle c x) 1 i j
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => simp only [assoc_first, lowerBlockLocalization_11, lowerBlockPair_11]
    | right j =>
      induction j using Fin.addCases with
      | left j => simp only [assoc_first, assoc_middle,
          lowerBlockLocalization_12, lowerBlockPair_12]
      | right j => simp only [assoc_first, assoc_last,
          lowerBlockLocalization_13, lowerBlockPair_12]
  | right i =>
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        rw [assoc_middle, assoc_first, lowerBlockLocalization_21, lowerBlockPair_21]
        simp [extendRectangle]
      | right j =>
        induction j using Fin.addCases with
        | left j =>
          simp only [assoc_middle, lowerBlockLocalization_22, lowerBlockPair_22]
          simp [Matrix.one_apply]
        | right j =>
          rw [assoc_middle, assoc_last, lowerBlockLocalization_23, lowerBlockPair_22]
          have hne : i.castAdd c ≠ j.natAdd d := by
            intro he
            have hv := congrArg Fin.val he
            simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
            omega
          simp [hne]
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        rw [assoc_last, assoc_first, lowerBlockLocalization_31, lowerBlockPair_21]
        simp [extendRectangle]
      | right j =>
        induction j using Fin.addCases with
        | left j =>
          rw [assoc_last, assoc_middle, lowerBlockLocalization_32, lowerBlockPair_22]
          have hne : i.natAdd d ≠ j.castAdd c := by
            intro he
            have hv := congrArg Fin.val he
            simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
            omega
          simp [hne]
        | right j =>
          simp only [assoc_last, lowerBlockLocalization_33, lowerBlockPair_22]
          simp [Matrix.one_apply]

/-- Each row in the final identity block is the corresponding standard
basis row of the full matrix. -/
theorem lowerBlockLocalization_final_row
    (g : Langlands.GeneralLinear a R) (x : Matrix (Fin d) (Fin a) R)
    (i : Fin c) (j : Fin (a + d + c)) :
    lowerBlockLocalization c g x 1 (lowerBlockLast a d i) j =
      (1 : Matrix (Fin (a + d + c)) (Fin (a + d + c)) R)
        (lowerBlockLast a d i) j := by
  induction j using Fin.addCases with
  | left j =>
    have hne : i.natAdd (a + d) ≠ j.castAdd c := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simp [lowerBlockLocalization, lowerBlockLast, rankInclusion, Matrix.one_apply, hne]
  | right j =>
    simp [lowerBlockLocalization, lowerBlockLast, rankInclusion, Matrix.one_apply]

/-- The appended zero rows give standard basis rows after the three blocks
have been reassociated. -/
theorem lowerBlockPair_extendRectangle_final_row
    (g : Langlands.GeneralLinear a R) (x : Matrix (Fin d) (Fin a) R)
    (i : Fin c) (j : Fin (a + (d + c))) :
    lowerBlockPair g (extendRectangle c x) 1 ((i.natAdd d).natAdd a) j =
      (1 : Matrix (Fin (a + (d + c))) (Fin (a + (d + c))) R)
        ((i.natAdd d).natAdd a) j := by
  induction j using Fin.addCases with
  | left j =>
    have hne : (i.natAdd d).natAdd a ≠ j.castAdd (d + c) := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    rw [lowerBlockPair_21]
    simp [extendRectangle, hne]
  | right j => simp [Matrix.one_apply]

section Subring

variable {F : Type u} [Field F] (O : Subring F) {n : ℕ}

/-- Integral adjacent ratios and an integral final diagonal entry force
all diagonal entries to be integral. -/
theorem diagonal_mem_of_roots
    (b : Fin (n + 1) → Fˣ) (hlast : (b (Fin.last n) : F) ∈ O)
    (hroot : ∀ i : Fin n, ((b i.castSucc / b i.succ : Fˣ) : F) ∈ O) :
    ∀ i, (b i : F) ∈ O := by
  intro i
  induction i using Fin.reverseInduction with
  | last => exact hlast
  | @cast i ih =>
    have h := O.mul_mem (hroot i) ih
    simpa only [← Units.val_mul, div_mul_cancel] using h

/-- If a matrix row is a standard basis row, its triangular left factor's
diagonal entry is an entry of the inverse right factor. -/
theorem diagonal_eq_inverse_of_standard_row
    {n : ℕ} (G B K : Langlands.GeneralLinear n F) (i : Fin n)
    (hG : ∀ j, G i j = (1 : Matrix (Fin n) (Fin n) F) i j)
    (hfac : G = B * K) :
    B i i = K⁻¹ i i := by
  have hB : B = G * K⁻¹ := by rw [hfac, mul_inv_cancel_right]
  rw [hB]
  change (G.val * (K⁻¹).val) i i = _
  simp [Matrix.mul_apply, hG, Matrix.one_apply]

/-- Integral inverse entries force an integral diagonal entry at every
standard basis row of the matrix. -/
theorem diagonal_mem_of_standard_row
    {n : ℕ} (G B K : Langlands.GeneralLinear n F) (i : Fin n)
    (hG : ∀ j, G i j = (1 : Matrix (Fin n) (Fin n) F) i j)
    (hfac : G = B * K) (hKinv : ∀ p q, K⁻¹ p q ∈ O) :
    B i i ∈ O := by
  rw [diagonal_eq_inverse_of_standard_row G B K i hG hfac]
  exact hKinv i i

end Subring

section IntegralTrailingRoots

variable {F : Type u} [Field F] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation F Γ₀) {a d : ℕ}

/-- At an unramified finite place, integral trailing simple roots force
integral rectangular coordinates in the actual three-block chart. -/
theorem lowerBlockLocalization_coordinate_mem_integer_of_trailingRoots
    (g : Langlands.GeneralLinear a F) (x : Matrix (Fin d) (Fin a) F)
    (B K : Langlands.GeneralLinear (a + (d + 1)) F)
    (hB : B.val.IsUpperTriangular) (hK : ∀ i j, K i j ∈ w.integer)
    (hKinv : ∀ i j, K⁻¹ i j ∈ w.integer)
    (hfac : reindex (finCongr (Nat.add_assoc a d 1))
      (lowerBlockLocalization 1 g x 1) = B * K)
    (hroot : ∀ i : Fin d,
      (B (i.castSucc.natAdd a) (i.castSucc.natAdd a) /
        B (i.succ.natAdd a) (i.succ.natAdd a)) ∈ w.integer)
    (i : Fin d) (j : Fin a) :
    x i j ∈ w.integer := by
  have hfac' : lowerBlockPair g (extendRectangle 1 x) 1 = B * K := by
    rwa [lowerBlockLocalization_reindex] at hfac
  let b : Fin (d + 1) → Fˣ := fun q =>
    Global.PrimitiveAdelicHeight.diagonalUnit B hB (q.natAdd a)
  have hlastIndex : (0 : Fin 1).natAdd d = Fin.last d := by
    apply Fin.ext
    simp
  have hrow :
      ∀ q, lowerBlockPair g (extendRectangle 1 x) 1 ((Fin.last d).natAdd a) q =
        (1 : Matrix (Fin (a + (d + 1))) (Fin (a + (d + 1))) F)
          ((Fin.last d).natAdd a) q := by
    intro q
    rw [← hlastIndex]
    exact lowerBlockPair_extendRectangle_final_row g x (0 : Fin 1) q
  have hlast : (b (Fin.last d) : F) ∈ w.integer :=
    diagonal_mem_of_standard_row w.integer
      (lowerBlockPair g (extendRectangle 1 x) 1) B K
      ((Fin.last d).natAdd a) hrow hfac' hKinv
  have hb : ∀ q, (b q : F) ∈ w.integer :=
    diagonal_mem_of_roots w.integer b hlast (fun q => by
      rw [Units.val_div_eq_div_val]
      dsimp only [b, Global.PrimitiveAdelicHeight.diagonalUnit]
      exact hroot q)
  have hprod : w (trailingDiagonalProduct a (d + 1) B.val) ≤ 1 := by
    apply (w.mem_integer_iff _).mp
    exact w.integer.prod_mem (fun q _ => hb q)
  have hx := lowerBlockPair_coordinate_mem_integer w g (extendRectangle 1 x)
    B.val K.val hB hK (congrArg Units.val hfac') hprod (i.castAdd 1) j
  simpa [extendRectangle] using hx

end IntegralTrailingRoots

end Langlands.GeneralLinear.RectangularIwasawa
