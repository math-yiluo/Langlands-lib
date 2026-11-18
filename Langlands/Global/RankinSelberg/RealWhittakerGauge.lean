import Langlands.Global.RankinSelberg.RealLocalWhittakerProperties
import Langlands.Global.RankinSelberg.RealIwasawa
import Langlands.Representation.Archimedean.RealStandardModuleFourier

/-! # The gauge estimate for uniformly regular real Whittaker functions -/

noncomputable section

open scoped Manifold ContDiff Real Matrix.Norms.Operator
open Matrix

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealWhittakerGauge

open Langlands.Archimedean (unitaryCompact matrixExpUnit rightDerivative matrixModel)
open RealLocalWhittaker (iteratedRightDerivative regularFunctions)

variable {r : ℕ}

/-! ### Square-zero one-parameter subgroups -/

theorem exp_smul_of_mul_self_eq_zero {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℝ} (hY : Y * Y = 0)
    (s : ℝ) : NormedSpace.exp (s • Y) = 1 + s • Y := by
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  beta_reduce
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ]
  · intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    rw [pow_add, pow_two, smul_mul_smul_comm, hY, smul_zero, mul_zero, smul_zero]

/-- The elementary matrix `E_(i,i+1)` of the simple root `i`. -/
def rootMatrix (i : Fin r) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  Matrix.single i.castSucc i.succ 1

theorem rootMatrix_mul_self (i : Fin r) : rootMatrix i * rootMatrix i = 0 := by
  unfold rootMatrix
  rw [Matrix.single_mul_single_of_ne]
  exact (Fin.castSucc_lt_succ (i := i)).ne'

/-- The direction `g⁻¹ E_(i,i+1) g`. -/
def conjRoot (g : Langlands.GeneralLinear (r + 1) ℝ) (i : Fin r) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  ((g⁻¹ : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) *
    rootMatrix i * (g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)

theorem conjRoot_mul_self (g : Langlands.GeneralLinear (r + 1) ℝ) (i : Fin r) :
    conjRoot g i * conjRoot g i = 0 := by
  unfold conjRoot
  calc
    _ = ((g⁻¹ : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) *
        rootMatrix i * ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) *
          ((g⁻¹ : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) *
        rootMatrix i * (g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by
      rw [Units.mul_inv, Matrix.mul_one, Matrix.mul_assoc _ (rootMatrix i) (rootMatrix i),
        rootMatrix_mul_self, Matrix.mul_zero, Matrix.zero_mul]

theorem mul_matrixExpUnit_conjRoot (g : Langlands.GeneralLinear (r + 1) ℝ) (i : Fin r) (s : ℝ) :
    g * matrixExpUnit (r + 1) (s • conjRoot g i) = matrixExpUnit (r + 1) (s • rootMatrix i) * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Langlands.Archimedean.matrixExpUnit_val,
    Langlands.Archimedean.matrixExpUnit_val, exp_smul_of_mul_self_eq_zero (conjRoot_mul_self g i),
    exp_smul_of_mul_self_eq_zero (rootMatrix_mul_self i)]
  unfold conjRoot
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem matrixExpUnit_rootMatrix_val (i : Fin r) (s : ℝ) :
    ((matrixExpUnit (r + 1) (s • rootMatrix i) : Langlands.GeneralLinear (r + 1) ℝ) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) = 1 + s • rootMatrix i := by
  rw [Langlands.Archimedean.matrixExpUnit_val, exp_smul_of_mul_self_eq_zero (rootMatrix_mul_self i)]

theorem rootMatrix_apply (i : Fin r) (p q : Fin (r + 1)) :
    rootMatrix i p q = if i.castSucc = p ∧ i.succ = q then 1 else 0 := by
  unfold rootMatrix
  rw [Matrix.single_apply]

theorem matrixExpUnit_rootMatrix_mem (i : Fin r) (s : ℝ) :
    matrixExpUnit (r + 1) (s • rootMatrix i) ∈ GeneralLinear.upperUnipotent (r + 1) ℝ := by
  refine ⟨fun p q hpq => ?_, fun p => ?_⟩
  · change ((matrixExpUnit (r + 1) (s • rootMatrix i) : Langlands.GeneralLinear (r + 1) ℝ) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) p q = 0
    change q < p at hpq
    rw [matrixExpUnit_rootMatrix_val, Matrix.add_apply, Matrix.smul_apply, rootMatrix_apply,
      Matrix.one_apply_ne (ne_of_lt hpq).symm]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact absurd hpq (not_lt.mpr (Fin.castSucc_lt_succ (i := i)).le)
    · simp
  · change ((matrixExpUnit (r + 1) (s • rootMatrix i) : Langlands.GeneralLinear (r + 1) ℝ) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) p p = 1
    rw [matrixExpUnit_rootMatrix_val, Matrix.add_apply, Matrix.smul_apply, rootMatrix_apply,
      Matrix.one_apply_eq]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      exact absurd (h1.trans h2.symm) (Fin.castSucc_lt_succ (i := i)).ne
    · simp

theorem realWhittakerCharacter_matrixExpUnit_rootMatrix (a : ℝˣ) (i : Fin r) (s : ℝ) :
    realWhittakerCharacter a (matrixExpUnit (r + 1) (s • rootMatrix i)) =
      (LocalFactor.Archimedean.realScaledCharacter a).complex s := by
  unfold realWhittakerCharacter
  congr 1
  rw [matrixExpUnit_rootMatrix_val, Finset.sum_eq_single i]
  · rw [Matrix.add_apply, Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne, Matrix.smul_apply,
      rootMatrix_apply]
    simp
  · intro j _ hj
    have hne : ¬(i.castSucc = j.castSucc ∧ i.succ = j.succ) := by
      rintro ⟨h1, -⟩
      exact hj (Fin.castSucc_injective _ h1).symm
    rw [Matrix.add_apply, Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := j)).ne, Matrix.smul_apply,
      rootMatrix_apply]
    have hij : i ≠ j := fun h => hj h.symm
    simp [hij]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The derivative of the scaled real character at the origin. -/
theorem hasDerivAt_realScaledCharacter (a : ℝˣ) :
    HasDerivAt (fun s : ℝ => (LocalFactor.Archimedean.realScaledCharacter a).complex s)
      (2 * π * (a : ℝ) * Complex.I) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => ((2 * π * ((a : ℝ) * t) : ℝ) : ℂ))
      ((2 * π * (a : ℝ) : ℝ) : ℂ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul (a : ℝ)).const_mul (2 * π)
    simpa using this.ofReal_comp
  have h2 := (h1.mul_const Complex.I).cexp
  simp only [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    LocalFactor.Archimedean.realScaledCharacter_apply, Real.fourierChar_apply]
  convert h2 using 1
  simp

/-! ### The one-step derivative identity -/

/-- Along the conjugated root direction, the right derivative of a character-equivariant
function is the character's derivative times the function. -/
theorem rightDerivative_conjRoot {a : ℝˣ} {F : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hF : F ∈ regularFunctions r a) (g : Langlands.GeneralLinear (r + 1) ℝ) (i : Fin r) :
    rightDerivative (matrixModel ℝ (r + 1)) (conjRoot g i) F g =
      2 * π * (a : ℝ) * Complex.I * F g := by
  have h1 := Langlands.Archimedean.hasDerivAt_mul_matrixExpUnit_smul
    (hF.2.1.of_le (by norm_num)) g (conjRoot g i)
  have h2 : (fun s : ℝ => F (g * matrixExpUnit (r + 1) (s • conjRoot g i))) =
      fun s => (LocalFactor.Archimedean.realScaledCharacter a).complex s * F g := by
    funext s
    rw [mul_matrixExpUnit_conjRoot, hF.1 _ (matrixExpUnit_rootMatrix_mem i s),
      realWhittakerCharacter_matrixExpUnit_rootMatrix]
  rw [h2] at h1
  exact h1.unique ((hasDerivAt_realScaledCharacter a).mul_const (F g))

/-! ### Expansion of a right derivative in elementary directions -/

/-- The right derivative of a fixed function as an additive map of the direction. -/
def rightDerivativeHom (F : Langlands.GeneralLinear (r + 1) ℝ → ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ →+ (Langlands.GeneralLinear (r + 1) ℝ → ℂ) :=
  AddMonoidHom.mk' (fun X => rightDerivative (matrixModel ℝ (r + 1)) X F)
    (fun X Y => Langlands.Archimedean.rightDerivative_add_left X Y F)

theorem rightDerivative_eq_sum (F : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) :
    rightDerivative (matrixModel ℝ (r + 1)) X F =
      ∑ p, ∑ q, X p q • rightDerivative (matrixModel ℝ (r + 1)) (Matrix.single p q 1) F := by
  have hX : rightDerivative (matrixModel ℝ (r + 1)) X F =
      rightDerivativeHom F (∑ p, ∑ q, Matrix.single p q (X p q)) := by
    rw [← Matrix.matrix_eq_sum_single X]
    rfl
  rw [hX, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hs : Matrix.single p q (X p q) = X p q • Matrix.single p q (1 : ℝ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  change rightDerivative (matrixModel ℝ (r + 1)) (Matrix.single p q (X p q)) F = _
  rw [hs, Langlands.Archimedean.rightDerivative_smul_left]

theorem norm_rightDerivative_le (F : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (g : Langlands.GeneralLinear (r + 1) ℝ) :
    ‖rightDerivative (matrixModel ℝ (r + 1)) X F g‖ ≤
      ∑ p, ∑ q, |X p q| *
        ‖rightDerivative (matrixModel ℝ (r + 1)) (Matrix.single p q 1) F g‖ := by
  rw [rightDerivative_eq_sum, Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]

/-! ### Iterating the identity along a list of simple roots -/

/-- The size of the conjugated root direction. -/
def rootSize (g : Langlands.GeneralLinear (r + 1) ℝ) (i : Fin r) : ℝ :=
  ∑ p, ∑ q, |conjRoot g i p q|

theorem rootSize_nonneg (g : Langlands.GeneralLinear (r + 1) ℝ) (i : Fin r) :
    0 ≤ rootSize g i :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Each simple root in the list contributes a factor `rootSize g i`, at the cost of one more
right derivative, which keeps the common growth exponent. -/
theorem exists_bound_list {a : ℝˣ} {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hreg : ∀ Xs, iteratedRightDerivative r Xs W ∈ regularFunctions r a) {N : ℕ}
    (hN : ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖iteratedRightDerivative r Xs W g‖ ≤ C * realMatrixHeight g ^ N)
    (is : List (Fin r)) :
    ∀ Ys, ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖iteratedRightDerivative r Ys W g‖ ≤
      C * (is.map (rootSize g)).prod * realMatrixHeight g ^ N := by
  induction is with
  | nil =>
    intro Ys
    obtain ⟨C, hC0, hC⟩ := hN Ys
    exact ⟨C, hC0, fun g => by simpa using hC g⟩
  | cons i is ih =>
    intro Ys
    choose C hC0 hC using fun pq : Fin (r + 1) × Fin (r + 1) =>
      ih (Matrix.single pq.1 pq.2 1 :: Ys)
    have hD0 : 0 ≤ ∑ pq, C pq := Finset.sum_nonneg fun pq _ => hC0 pq
    have ha : 0 < 2 * π * |(a : ℝ)| := by
      have := abs_pos.mpr a.ne_zero
      positivity
    refine ⟨(∑ pq, C pq) / (2 * π * |(a : ℝ)|), div_nonneg hD0 ha.le, fun g => ?_⟩
    have hP : 0 ≤ (is.map (rootSize g)).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
        exact rootSize_nonneg g j
    have hH : 0 ≤ realMatrixHeight g ^ N :=
      pow_nonneg (RealPlaceRestriction.realMatrixHeight_nonneg g) N
    have key := rightDerivative_conjRoot (hreg Ys) g i
    have h1 : ‖iteratedRightDerivative r Ys W g‖ * (2 * π * |(a : ℝ)|) =
        ‖rightDerivative (matrixModel ℝ (r + 1)) (conjRoot g i)
          (iteratedRightDerivative r Ys W) g‖ := by
      rw [key]
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_ofNat, abs_of_pos Real.pi_pos]
      ring
    have h2 : ‖rightDerivative (matrixModel ℝ (r + 1)) (conjRoot g i)
          (iteratedRightDerivative r Ys W) g‖ ≤
        rootSize g i * ((∑ pq, C pq) * (is.map (rootSize g)).prod *
          realMatrixHeight g ^ N) := by
      refine (norm_rightDerivative_le _ _ g).trans ?_
      rw [rootSize, Finset.sum_mul]
      refine Finset.sum_le_sum fun p _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun q _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc
        ‖rightDerivative (matrixModel ℝ (r + 1)) (Matrix.single p q 1)
            (iteratedRightDerivative r Ys W) g‖ =
            ‖iteratedRightDerivative r (Matrix.single p q 1 :: Ys) W g‖ := rfl
        _ ≤ C (p, q) * (is.map (rootSize g)).prod * realMatrixHeight g ^ N := hC (p, q) g
        _ ≤ (∑ pq, C pq) * (is.map (rootSize g)).prod * realMatrixHeight g ^ N := by
          gcongr
          exact Finset.single_le_sum (f := C) (fun pq _ => hC0 pq) (Finset.mem_univ (p, q))
    rw [List.map_cons, List.prod_cons]
    have h3 := h1.trans_le h2
    calc
      ‖iteratedRightDerivative r Ys W g‖ =
          ‖iteratedRightDerivative r Ys W g‖ * (2 * π * |(a : ℝ)|) / (2 * π * |(a : ℝ)|) := by
        field_simp
      _ ≤ rootSize g i * ((∑ pq, C pq) * (is.map (rootSize g)).prod *
          realMatrixHeight g ^ N) / (2 * π * |(a : ℝ)|) := by gcongr
      _ = _ := by ring

theorem exists_list_prod (m : Fin r → ℕ) :
    ∃ is : List (Fin r), ∀ f : Fin r → ℝ, (is.map f).prod = ∏ i, f i ^ m i := by
  refine ⟨(List.ofFn fun i => List.replicate (m i) i).flatten, fun f => ?_⟩
  rw [List.map_flatten, List.prod_flatten, List.map_ofFn, List.map_ofFn, List.prod_ofFn]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [List.map_replicate, List.prod_replicate]

/-! ### Entries on the torus times the orthogonal group -/

open RealIwasawa (torus torus_val torus_neg)

theorem conjRoot_apply (g : Langlands.GeneralLinear (r + 1) ℝ) (i : Fin r) (p q : Fin (r + 1)) :
    conjRoot g i p q =
      ((g⁻¹ : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
          p i.castSucc *
        (g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i.succ q := by
  unfold conjRoot rootMatrix
  rw [Matrix.mul_apply, Finset.sum_eq_single i.succ]
  · rw [Matrix.mul_single_apply_same, mul_one]
  · intro b _ hb
    rw [Matrix.mul_single_apply_of_ne (hbj := hb), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem abs_unitary_entry_le (k : unitaryCompact ℝ (r + 1)) (p q : Fin (r + 1)) :
    |((k : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) p q| ≤ 1 := by
  have hU : ((k : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) ∈
      Matrix.unitaryGroup (Fin (r + 1)) ℝ := k.2
  have := entry_norm_bound_of_unitary hU p q
  rwa [Real.norm_eq_abs] at this

theorem abs_unitary_inv_entry_le (k : unitaryCompact ℝ (r + 1)) (p q : Fin (r + 1)) :
    |(((k : Langlands.GeneralLinear (r + 1) ℝ)⁻¹ : Langlands.GeneralLinear (r + 1) ℝ) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) p q| ≤ 1 :=
  abs_unitary_entry_le ⟨_, (unitaryCompact ℝ (r + 1)).inv_mem k.2⟩ p q

theorem torus_mul_val_apply (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1))
    (p q : Fin (r + 1)) :
    ((torus y * (k : Langlands.GeneralLinear (r + 1) ℝ) : Langlands.GeneralLinear (r + 1) ℝ) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) p q =
      Real.exp (y p) *
        ((k : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) p q := by
  rw [Units.val_mul, torus_val, Matrix.diagonal_mul]

theorem torus_mul_inv_val_apply (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1))
    (p q : Fin (r + 1)) :
    (((torus y * (k : Langlands.GeneralLinear (r + 1) ℝ))⁻¹ : Langlands.GeneralLinear (r + 1) ℝ) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) p q =
      (((k : Langlands.GeneralLinear (r + 1) ℝ)⁻¹ : Langlands.GeneralLinear (r + 1) ℝ) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) p q * Real.exp (-y q) := by
  have h : (((torus y * (k : Langlands.GeneralLinear (r + 1) ℝ))⁻¹ :
      Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) =
      (((k : Langlands.GeneralLinear (r + 1) ℝ)⁻¹ : Langlands.GeneralLinear (r + 1) ℝ) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) * Matrix.diagonal fun i => Real.exp ((-y) i) := by
    rw [_root_.mul_inv_rev, ← torus_neg, Units.val_mul, torus_val]
  rw [h, Matrix.mul_diagonal]
  try simp only [Pi.neg_apply]

theorem abs_conjRoot_torus_mul_le (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)) (i : Fin r)
    (p q : Fin (r + 1)) :
    |conjRoot (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ)) i p q| ≤ Real.exp (y i.succ - y i.castSucc) := by
  rw [conjRoot_apply, torus_mul_inv_val_apply, torus_mul_val_apply, abs_mul, abs_mul, abs_mul,
    Real.abs_exp, Real.abs_exp]
  have h1 := abs_unitary_inv_entry_le k p i.castSucc
  have h2 := abs_unitary_entry_le k i.succ q
  calc
    _ ≤ 1 * Real.exp (-y i.castSucc) * (Real.exp (y i.succ) * 1) := by gcongr
    _ = Real.exp (y i.succ - y i.castSucc) := by
      rw [one_mul, mul_one, ← Real.exp_add, neg_add_eq_sub]

theorem rootSize_torus_mul_le (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)) (i : Fin r) :
    rootSize (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ)) i ≤ ((r : ℝ) + 1) ^ 2 * Real.exp (y i.succ - y i.castSucc) := by
  unfold rootSize
  calc
    _ ≤ ∑ _p : Fin (r + 1), ∑ _q : Fin (r + 1), Real.exp (y i.succ - y i.castSucc) :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ =>
        abs_conjRoot_torus_mul_le y k i p q
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

theorem sq_exp_mul_le {c t S : ℝ} (hc : |c| ≤ 1) (ht : t ≤ S) :
    ‖Real.exp t * c‖ ^ 2 ≤ Real.exp (2 * S) := by
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  calc
    (Real.exp t * |c|) ^ 2 ≤ (Real.exp t * 1) ^ 2 := by gcongr
    _ = Real.exp (t + t) := by rw [mul_one, sq, Real.exp_add]
    _ ≤ Real.exp (2 * S) := Real.exp_le_exp.mpr (by linarith)

theorem realMatrixHeight_torus_mul_le (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)) :
    realMatrixHeight (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ)) ≤
      2 * ((r : ℝ) + 1) ^ 2 * Real.exp (2 * ∑ j, |y j|) := by
  have hy : ∀ j, |y j| ≤ ∑ j, |y j| := fun j =>
    Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  unfold realMatrixHeight
  calc
    _ ≤ ∑ _p : Fin (r + 1), ∑ _q : Fin (r + 1), 2 * Real.exp (2 * ∑ j, |y j|) := by
      refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
      rw [two_mul (Real.exp _)]
      refine add_le_add ?_ ?_
      · rw [torus_mul_val_apply]
        exact sq_exp_mul_le (abs_unitary_entry_le k p q) ((le_abs_self _).trans (hy p))
      · rw [torus_mul_inv_val_apply, mul_comm]
        exact sq_exp_mul_le (abs_unitary_inv_entry_le k p q) ((neg_le_abs _).trans (hy q))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

theorem realMatrixHeight_torus_mul_pow_le (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1))
    (N : ℕ) :
    realMatrixHeight (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ)) ^ N ≤
      (2 * ((r : ℝ) + 1) ^ 2) ^ N * Real.exp (((2 * N : ℕ) : ℝ) * ∑ j, |y j|) := by
  calc
    _ ≤ (2 * ((r : ℝ) + 1) ^ 2 * Real.exp (2 * ∑ j, |y j|)) ^ N :=
      pow_le_pow_left₀ (RealPlaceRestriction.realMatrixHeight_nonneg _)
        (realMatrixHeight_torus_mul_le y k) N
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring

theorem rootSize_pow_le (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)) (i : Fin r)
    (S : Finset (Fin r)) (hS : i ∈ S ↔ 0 ≤ y i.castSucc - y i.succ) (M : ℕ) :
    rootSize (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ)) i ^ (if i ∈ S then M else 0) ≤
      (((r : ℝ) + 1) ^ 2) ^ M * Real.exp (-(M : ℝ) * max (y i.castSucc - y i.succ) 0) := by
  have hb : 1 ≤ ((r : ℝ) + 1) ^ 2 :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
  split_ifs with hi
  · rw [max_eq_left (hS.mp hi)]
    calc
      rootSize (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ)) i ^ M ≤
          (((r : ℝ) + 1) ^ 2 * Real.exp (y i.succ - y i.castSucc)) ^ M :=
        pow_le_pow_left₀ (rootSize_nonneg _ _) (rootSize_torus_mul_le y k i) M
      _ = _ := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
  · have h0 : y i.castSucc - y i.succ < 0 := lt_of_not_ge fun h => hi (hS.mpr h)
    rw [max_eq_right h0.le, mul_zero, Real.exp_zero, mul_one, pow_zero]
    exact one_le_pow₀ hb

theorem prod_rootSize_pow_le (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)) (M : ℕ) :
    ∏ i : Fin r, rootSize (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ)) i ^
        (if i ∈ Finset.univ.filter (fun i : Fin r => 0 ≤ y i.castSucc - y i.succ) then M else 0) ≤
      ((((r : ℝ) + 1) ^ 2) ^ M) ^ r *
        Real.exp (-(M : ℝ) * ∑ i : Fin r, max (y i.castSucc - y i.succ) 0) := by
  calc
    _ ≤ ∏ i : Fin r, ((((r : ℝ) + 1) ^ 2) ^ M *
          Real.exp (-(M : ℝ) * max (y i.castSucc - y i.succ) 0)) :=
      Finset.prod_le_prod₀ (fun i _ => pow_nonneg (rootSize_nonneg _ _) _)
        (fun i _ => rootSize_pow_le y k i _ (by simp) M)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_sum, Finset.mul_sum]

/-! ### The gauge estimate -/

/-- **Gauge estimate.** If all iterated right derivatives of `W` are character-equivariant,
smooth and polynomially bounded with one common exponent, then on `torus y * k` the function
`W` decays faster than any exponential in the positive parts of the simple-root coordinates
`y_i - y_(i+1)`, at the cost of a fixed exponential factor in `∑ |y_j|`. -/
theorem exists_gauge_bound {a : ℝˣ} {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hreg : ∀ Xs, iteratedRightDerivative r Xs W ∈ regularFunctions r a)
    (hgrowth : ∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖iteratedRightDerivative r Xs W g‖ ≤ C * realMatrixHeight g ^ N) :
    ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)),
        ‖W (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ))‖ ≤ C * Real.exp (-(M : ℝ) * ∑ i : Fin r, max (y i.castSucc - y i.succ) 0 +
          (N : ℝ) * ∑ j, |y j|) := by
  obtain ⟨N, hN⟩ := hgrowth
  refine ⟨2 * N, fun M => ?_⟩
  have hS : ∀ S : Finset (Fin r), ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖W g‖ ≤
      C * (∏ i : Fin r, rootSize g i ^ (if i ∈ S then M else 0)) * realMatrixHeight g ^ N := by
    intro S
    obtain ⟨is, his⟩ := exists_list_prod fun i : Fin r => if i ∈ S then M else 0
    have his' : ∀ f : Fin r → ℝ,
        (is.map f).prod = ∏ i, f i ^ (if i ∈ S then M else 0) := his
    obtain ⟨C, hC0, hC⟩ := exists_bound_list hreg hN is []
    refine ⟨C, hC0, fun g => ?_⟩
    rw [← his' (rootSize g)]
    exact hC g
  choose C hC0 hC using hS
  have hD0 : 0 ≤ ∑ S, C S := Finset.sum_nonneg fun S _ => hC0 S
  refine ⟨(∑ S, C S) * ((((r : ℝ) + 1) ^ 2) ^ M) ^ r * (2 * ((r : ℝ) + 1) ^ 2) ^ N,
    mul_nonneg (mul_nonneg hD0 (by positivity)) (by positivity), fun y k => ?_⟩
  have h1 := hC (Finset.univ.filter fun i : Fin r => 0 ≤ y i.castSucc - y i.succ) (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ))
  have h2 := prod_rootSize_pow_le y k M
  have h3 := realMatrixHeight_torus_mul_pow_le y k N
  have hCS : C (Finset.univ.filter fun i : Fin r => 0 ≤ y i.castSucc - y i.succ) ≤ ∑ S, C S :=
    Finset.single_le_sum (fun S _ => hC0 S) (Finset.mem_univ _)
  have hP0 : 0 ≤ ∏ i : Fin r, rootSize (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ)) i ^
      (if i ∈ Finset.univ.filter (fun i : Fin r => 0 ≤ y i.castSucc - y i.succ) then M else 0) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (rootSize_nonneg _ _) _
  calc
    ‖W (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ))‖ ≤ _ := h1
    _ ≤ (∑ S, C S) * (((((r : ℝ) + 1) ^ 2) ^ M) ^ r *
          Real.exp (-(M : ℝ) * ∑ i : Fin r, max (y i.castSucc - y i.succ) 0)) *
        ((2 * ((r : ℝ) + 1) ^ 2) ^ N * Real.exp (((2 * N : ℕ) : ℝ) * ∑ j, |y j|)) :=
      mul_le_mul (mul_le_mul hCS h2 hP0 hD0) h3
        (pow_nonneg (RealPlaceRestriction.realMatrixHeight_nonneg _) _)
        (mul_nonneg hD0 (by positivity))
    _ = _ := by
      rw [Real.exp_add]
      ring

end Langlands.Global.RankinSelbergGlobal.RealWhittakerGauge
