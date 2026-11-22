import Langlands.Global.RankinSelberg.ComplexGapTailEndpoints
import Langlands.Global.RankinSelberg.ComplexGapTailMatrix
import Langlands.Global.RankinSelberg.ComplexGapLeadingSchwartz

/-! # Domination of the complex inverse-transpose tail -/

noncomputable section

open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapInverseTransposeTailBound

open Langlands.Archimedean (unitaryCompact)
open ComplexTwoBlockHaar (tailBlockIndex rightTail blockLog complexGapTailMatrix)
open ComplexGapTailEndpoints (firstTailColumn exp_le_endpoint_norms)
open ComplexGapTorusBound (blockLog_last exponent_le_first)
open ComplexLocalWhittakerGauge (logTorus logTorus_val)
open ComplexGapLeadingSchwartz (matrixDecay)
open RealConvergenceAnalysis (rootPos)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "Row" => fun n => Fin n → ℂ

variable {r k : ℕ} (hk : 0 < k) (hkn : k < r + 1)

local notation "n" => (r + 1)
local notation "d" => (r + 1 - k)

private def firstTailIndex : Fin d := ⟨0, Nat.sub_pos_of_lt hkn⟩
private def lastTailIndex : Fin d := ⟨r - k, by omega⟩

local notation "fstTail" => (firstTailIndex hkn)
local notation "lstTail" => (lastTailIndex hkn)

/-- The trailing columns of the inverse-transpose matrix in consecutive-block order. -/
def inverseTailColumns (g : G n) : Mat n d :=
  fun i j => g⁻¹.val (tailBlockIndex hkn (Sum.inr j)) i

private theorem firstColumn_apply (g : G n) (i : Fin n) :
    firstTailColumn hk hkn g i = g.val i (tailBlockIndex hkn (Sum.inr fstTail)) := rfl

private theorem eq_lastTailIndex : tailBlockIndex hkn (Sum.inr lstTail) = Fin.last r := by
  apply Fin.ext
  change k + (r - k) = r
  omega

private theorem norm_mul_entry_le {A B : Mat n n} (i j : Fin n) {a b : ℝ}
    (ha : 0 ≤ a)
    (hA : ∀ l, ‖A i l‖ ≤ a) (hB : ∀ l, ‖B l j‖ ≤ b) :
    ‖(A * B) i j‖ ≤ ((n : ℕ) : ℝ) * (a * b) := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ l, ‖A i l * B l j‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, a * b := Finset.sum_le_sum fun l _ => by
      rw [norm_mul]
      exact mul_le_mul (hA l) (hB l) (norm_nonneg _) ha
    _ = _ := by simp [nsmul_eq_mul]

/-- The physical first column controls the first rectangle column, while the inverse-transpose
trailing columns control the inverse tail block. -/
theorem alternateTail_norm_bounds (h : G d) (X : Mat k d) (q : KU n) :
    let g := rightTail hk hkn h X q
    ‖fun i => X i fstTail‖ ≤ ((n : ℕ) : ℝ) * ‖firstTailColumn hk hkn g‖ ∧
      ‖h⁻¹.val‖ ≤ ((n : ℕ) : ℝ) * ‖inverseTailColumns hkn g‖ := by
  let e := tailBlockIndex hkn
  let g := rightTail hk hkn h X q
  obtain ⟨hF, hI⟩ := complexGapTailMatrix n k hk hkn h X q
  dsimp only at hF hI
  have hn (i j : Fin n) : ‖q.val.val i j‖ ≤ 1 :=
    LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup q.2 i j
  have hn' (i j : Fin n) : ‖q.val⁻¹.val i j‖ ≤ 1 :=
    LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup (q⁻¹ : KU n).2 i j
  have hForward (i : Fin k) :
      (q.val⁻¹.val * g.val) (e (Sum.inl i)) (e (Sum.inr fstTail)) = X i fstTail := by
    rw [hF, ← Matrix.mul_assoc, q.val.inv_mul, Matrix.one_mul]
    simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₂]
  have hInverse (i j : Fin d) :
      (g⁻¹.val * q.val.val) (e (Sum.inr i)) (e (Sum.inr j)) = h⁻¹.val i j := by
    rw [hI, Matrix.mul_assoc, q.val.inv_mul, Matrix.mul_one]
    simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₂₂]
  change ‖fun i => X i fstTail‖ ≤ _ ∧ ‖h⁻¹.val‖ ≤ _
  constructor
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    rw [← hForward i]
    simpa only [one_mul] using
      norm_mul_entry_le (A := q.val⁻¹.val) (B := g.val) (e (Sum.inl i)) (e (Sum.inr fstTail))
        zero_le_one (hn' _) (fun l => by
          rw [← firstColumn_apply hk hkn g l]
          exact norm_le_pi_norm (firstTailColumn hk hkn g) l)
  · refine (Matrix.norm_le_iff (by positivity)).mpr fun i j => ?_
    rw [← hInverse i j]
    simpa only [mul_one] using norm_mul_entry_le (A := g⁻¹.val) (B := q.val.val) (e (Sum.inr i)) (e (Sum.inr j))
      (norm_nonneg (inverseTailColumns hkn g))
      (fun l => Matrix.norm_entry_le_entrywise_sup_norm (inverseTailColumns hkn g) (i := l) (j := i))
      (fun l => hn l _)

private theorem lastRow_norm_le_inverseTailColumns (g : G n) :
    ‖g⁻¹.val (Fin.last r)‖ ≤ ‖inverseTailColumns hkn g‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  rw [← eq_lastTailIndex hkn]
  exact Matrix.norm_entry_le_entrywise_sup_norm (inverseTailColumns hkn g) (i := i) (j := lstTail)

private theorem norm_unipotentInverse_le (z : Fin d → ℝ) (u : N d) :
    ‖u.val⁻¹.val‖ ≤ ‖(logTorus (-z) * u.val)⁻¹.val‖ * Real.exp (∑ j, |z j|) := by
  let h := logTorus (-z) * u.val
  have hEq : u.val⁻¹ = h⁻¹ * logTorus (-z) := by simp [h, mul_inv_rev]
  refine (Matrix.norm_le_iff (by positivity)).mpr fun i j => ?_
  rw [hEq, Units.val_mul, logTorus_val, Matrix.mul_diagonal, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _)]
  refine mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm h⁻¹.val)
    (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (norm_nonneg _)
  exact (neg_le_abs (z j)).trans (Finset.single_le_sum (fun l _ => abs_nonneg (z l)) (Finset.mem_univ j))

private theorem exists_alternateTail_exponential_bound
    (A B T R : ℝ) (hB : 0 ≤ B) (hT : A + 1 ≤ T) (p q : ℕ) :
    ∃ J P Q : ℕ, ∀ (y : Fin k → ℝ) (z : Fin d → ℝ) (u : N d) (X : Mat k d) (v : KU n),
      let g := rightTail hk hkn (logTorus (-z) * u.val) X v
      let Y := ∑ i, |y i|
      let Z := ∑ i, |z i|
      let U := ((n : ℕ) : ℝ) * (1 + ‖firstTailColumn hk hkn g‖)
      let V := ((n : ℕ) : ℝ) * (1 + ‖inverseTailColumns hkn g‖)
      Real.exp (A * Y + B * Z + T * (∑ i, y i) - (J : ℝ) * rootPos (blockLog hkn y z)) *
        (1 + ‖fun i => X i fstTail‖) ^ p * (1 + ‖u.val⁻¹.val‖) ^ q ≤
        Real.exp (-Y - R * Z) * U ^ (Q + p) * V ^ (P + q) := by
  let B' := B + (q : ℝ) + max R 0
  let P' := max (2 * T) (B' + 1) * ((r : ℝ) + 1)
  let Q' := (B' + 1) * (d : ℕ)
  obtain ⟨J, hJ⟩ := exists_nat_ge (P' + Q')
  obtain ⟨P, hP⟩ := exists_nat_ge P'
  obtain ⟨Q, hQ⟩ := exists_nat_ge Q'
  have hB' : 0 ≤ B' := by dsimp only [B']; positivity
  have hn : 1 ≤ ((n : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos r
  refine ⟨J, P, Q, fun y z u X v => ?_⟩
  let h := logTorus (-z) * u.val
  let g := rightTail hk hkn h X v
  let Y := ∑ i, |y i|
  let Z := ∑ i, |z i|
  let U := ((n : ℕ) : ℝ) * (1 + ‖firstTailColumn hk hkn g‖)
  let V := ((n : ℕ) : ℝ) * (1 + ‖inverseTailColumns hkn g‖)
  let E := A * Y + B * Z + T * (∑ i, y i) - (J : ℝ) * rootPos (blockLog hkn y z)
  have hU : 1 ≤ U := one_le_mul_of_one_le_of_one_le hn (le_add_of_nonneg_right (norm_nonneg _))
  have hV : 1 ≤ V := one_le_mul_of_one_le_of_one_le hn (le_add_of_nonneg_right (norm_nonneg _))
  have hUpos := zero_lt_one.trans_le hU
  have hVpos := zero_lt_one.trans_le hV
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨hFirst, hLast⟩ := exp_le_endpoint_norms hk hkn z u X v
  have hFirst' : max (-z fstTail) 0 ≤ Real.log U := by
    refine max_le ?_ (Real.log_nonneg hU)
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hUpos]
    exact hFirst.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity))
  have hLast' : max (z lstTail) 0 ≤ Real.log V := by
    refine max_le ?_ (Real.log_nonneg hV)
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hVpos]
    exact hLast.trans (mul_le_mul_of_nonneg_left
      ((lastRow_norm_le_inverseTailColumns hkn g).trans (le_add_of_nonneg_left zero_le_one))
      (by positivity))
  have hRoot : A * Y + B' * Z + T * (∑ i, y i) - (J : ℝ) * rootPos (blockLog hkn y z) -
      (P : ℝ) * max (z lstTail) 0 - (Q : ℝ) * max (-z fstTail) 0 ≤ -(Y + Z) := by
    have h := exponent_le_first hkn y z hB' hT hJ hP hQ
    dsimp only at h
    rw [blockLog_last] at h
    exact h
  have hExp : E + (q : ℝ) * Z ≤ -Y - R * Z + (Q : ℝ) * Real.log U + (P : ℝ) * Real.log V := by
    have h₁ := mul_le_mul_of_nonneg_left hFirst' (Nat.cast_nonneg Q : 0 ≤ (Q : ℝ))
    have h₂ := mul_le_mul_of_nonneg_left hLast' (Nat.cast_nonneg P : 0 ≤ (P : ℝ))
    have h₃ := mul_le_mul_of_nonneg_right (le_max_left R 0) hZ
    dsimp only [E, B'] at hRoot ⊢
    linarith only [hRoot, h₁, h₂, h₃, hZ]
  have hExp' := Real.exp_le_exp.mpr hExp
  rw [Real.exp_add E, Real.exp_nat_mul, Real.exp_add, Real.exp_add, Real.exp_nat_mul,
    Real.exp_nat_mul, Real.exp_log hUpos, Real.exp_log hVpos] at hExp'
  obtain ⟨hX, hI⟩ := alternateTail_norm_bounds hk hkn h X v
  have hX' : 1 + ‖fun i => X i fstTail‖ ≤ U := by
    dsimp only [U]
    rw [mul_add, mul_one]
    exact add_le_add hn hX
  have hI' : 1 + ‖u.val⁻¹.val‖ ≤ V * Real.exp Z := by
    have hu := (norm_unipotentInverse_le (r := r) (k := k) z u).trans
      (mul_le_mul_of_nonneg_right hI (Real.exp_nonneg _))
    dsimp only [V]
    rw [mul_add, mul_one, add_mul]
    apply add_le_add _ hu
    exact one_le_mul_of_one_le_of_one_le hn (Real.one_le_exp hZ)
  change Real.exp E * (1 + ‖fun i => X i fstTail‖) ^ p * (1 + ‖u.val⁻¹.val‖) ^ q ≤ _
  calc
    _ ≤ Real.exp E * U ^ p * (V * Real.exp Z) ^ q := by gcongr
    _ = (Real.exp E * (Real.exp Z) ^ q) * U ^ p * V ^ q := by
      rw [mul_pow V (Real.exp Z)]
      ac_rfl
    _ ≤ (Real.exp (-Y - R * Z) * U ^ Q * V ^ P) * U ^ p * V ^ q := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hExp' (by positivity))
        (by positivity)
    _ = _ := by dsimp only; rw [pow_add, pow_add]; ring

private theorem schwartz_one_add_norm_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : 𝓢(E, ℂ)) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖F x‖ * (1 + ‖x‖) ^ l ≤ C := by
  let S : Seminorm ℝ 𝓢(E, ℂ) := (Finset.Iic (l, 0)).sup fun p => SchwartzMap.seminorm ℝ p.1 p.2
  refine ⟨2 ^ l * S F, by positivity, fun x => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (l, 0)) le_rfl le_rfl F x
  simpa only [norm_iteratedFDeriv_zero, mul_comm ‖F x‖, S] using h

/-- Schwartz tests on the first physical column and inverse-transpose trailing columns
give rapid decay in the retained upper column, inverse unipotent tail and logarithmic tail. -/
def ComplexGapInverseTransposeTailBoundStatement : Prop :=
  ∀ (r k : ℕ) (hk : 0 < k) (hkn : k < r + 1) (A B T R : ℝ), 0 ≤ B → A + 1 ≤ T →
    ∀ (Φ : 𝓢(Row (r + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - k), ℂ)) (l m p q : ℕ),
      ∃ (J : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (y : Fin k → ℝ) (z : Fin (r + 1 - k) → ℝ) (u : N (r + 1 - k))
        (X : Mat k (r + 1 - k)) (v : KU (r + 1)),
        let g := rightTail hk hkn (logTorus (-z) * u.val) X v
        let Y := ∑ i, |y i|
        let Z := ∑ i, |z i|
        let U := 1 + ‖firstTailColumn hk hkn g‖
        let V := 1 + ‖inverseTailColumns hkn g‖
        ‖Φ (firstTailColumn hk hkn g) * Ξ (inverseTailColumns hkn g)‖ * U ^ l * V ^ m *
          Real.exp (A * Y + B * Z + T * (∑ i, y i) - (J : ℝ) * rootPos (blockLog hkn y z)) ≤
          C * Real.exp (-Y - R * Z) *
            ((1 + ‖fun i => X i ⟨0, Nat.sub_pos_of_lt hkn⟩‖) ^ p)⁻¹ * matrixDecay q u.val⁻¹.val

theorem complexGapInverseTransposeTailBound : ComplexGapInverseTransposeTailBoundStatement := by
  intro r k hk hkn A B T R hB hT Φ Ξ l m p q
  obtain ⟨J, P, Q, hExp⟩ := exists_alternateTail_exponential_bound hk hkn A B T R hB hT p q
  obtain ⟨C₁, hC₁, hf⟩ := schwartz_one_add_norm_pow Φ (l + (Q + p))
  obtain ⟨C₂, hC₂, hd⟩ := schwartz_one_add_norm_pow Ξ (m + (P + q))
  let c := ((r + 1 : ℕ) : ℝ) ^ (Q + p) * ((r + 1 : ℕ) : ℝ) ^ (P + q)
  refine ⟨J, c * C₁ * C₂, by dsimp only [c]; positivity, fun y z u X v => ?_⟩
  let g := rightTail hk hkn (logTorus (-z) * u.val) X v
  let Y := ∑ i, |y i|
  let Z := ∑ i, |z i|
  let U := 1 + ‖firstTailColumn hk hkn g‖
  let V := 1 + ‖inverseTailColumns hkn g‖
  let F := ‖Φ (firstTailColumn hk hkn g)‖
  let H := ‖Ξ (inverseTailColumns hkn g)‖
  let D₁ := (1 + ‖fun i => X i (⟨0, Nat.sub_pos_of_lt hkn⟩ : Fin (r + 1 - k))‖) ^ p
  let D₂ := (1 + ‖u.val⁻¹.val‖) ^ q
  let E := Real.exp (A * Y + B * Z + T * (∑ i, y i) - (J : ℝ) * rootPos (blockLog hkn y z))
  let E' := Real.exp (-Y - R * Z)
  have hD₁ : 0 < D₁ := by dsimp only [D₁]; positivity
  have hD₂ : 0 < D₂ := by dsimp only [D₂]; positivity
  have hB : E * D₁ * D₂ ≤ E' * c * U ^ (Q + p) * V ^ (P + q) := by
    have hb := hExp y z u X v
    change E * D₁ * D₂ ≤ E' * (((r + 1 : ℕ) : ℝ) * U) ^ (Q + p) *
      (((r + 1 : ℕ) : ℝ) * V) ^ (P + q) at hb
    refine hb.trans_eq ?_
    rw [mul_pow, mul_pow]
    dsimp only [c]
    ring
  have hF : F * U ^ (l + (Q + p)) ≤ C₁ := hf _
  have hH : H * V ^ (m + (P + q)) ≤ C₂ := hd _
  change ‖Φ _ * Ξ _‖ * U ^ l * V ^ m * E ≤ c * C₁ * C₂ * E' * D₁⁻¹ * D₂⁻¹
  rw [norm_mul, ← div_eq_mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ hD₂).mpr
  apply (le_div_iff₀ hD₁).mpr
  change F * H * U ^ l * V ^ m * E * D₂ * D₁ ≤ _
  calc
    _ = (F * H * U ^ l * V ^ m) * (E * D₁ * D₂) := by ring
    _ ≤ (F * H * U ^ l * V ^ m) * (E' * c * U ^ (Q + p) * V ^ (P + q)) := by
      exact mul_le_mul_of_nonneg_left hB (by dsimp only [F, H, U, V]; positivity)
    _ = (F * U ^ (l + (Q + p))) * (H * V ^ (m + (P + q))) * (c * E') := by
      rw [pow_add, pow_add]
      ring
    _ ≤ (C₁ * C₂) * (c * E') := by
      have h := mul_le_mul hF hH (by dsimp only [H, V]; positivity) hC₁
      exact mul_le_mul_of_nonneg_right h (by dsimp only [c, E']; positivity)
    _ = _ := by ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapInverseTransposeTailBound
