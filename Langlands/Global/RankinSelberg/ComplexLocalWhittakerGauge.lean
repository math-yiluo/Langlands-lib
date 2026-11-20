import Langlands.Global.RankinSelberg.ComplexLocalWhittakerGrowth
import Langlands.Representation.Archimedean.ComplexDuality.UnitaryHaar
import Langlands.Representation.Whittaker.Iwasawa

/-! # Simple-root majorization for complex local Whittaker functions -/

noncomputable section
open scoped Classical Matrix.Norms.Operator
open Langlands.Archimedean Langlands.LocalFactor.Archimedean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal
namespace ComplexLocalWhittakerGauge

/-- The diagonal matrix with entries `exp (y i)`, viewed in the complex group. -/
def logTorus {n : ℕ} (y : Fin n → ℝ) : Langlands.GeneralLinear n ℂ :=
  GeneralLinear.Iwasawa.diagonalUnits fun i =>
    Units.mk0 (Real.exp (y i) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

@[simp] theorem logTorus_val {n : ℕ} (y : Fin n → ℝ) :
    (logTorus y).val = Matrix.diagonal (fun i => (Real.exp (y i) : ℂ)) := rfl

@[simp] theorem logTorus_inv_val {n : ℕ} (y : Fin n → ℝ) :
    (logTorus y)⁻¹.val = Matrix.diagonal (fun i => (Real.exp (-y i) : ℂ)) := by
  change Matrix.diagonal (fun i => (Real.exp (y i) : ℂ)⁻¹) = _
  simp [Real.exp_neg]

section RootDerivative

variable {r : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "V" => complexWhittakerModel r ds a
local notation "R" => complexWhittakerRightDerivative r ds a

private def root (i : Fin r) (z : ℂ) : Mat :=
  Matrix.single i.castSucc i.succ z

private theorem root_strictUpper (i : Fin r) (z : ℂ) :
    ∀ p q, q ≤ p → root i z p q = 0 := by
  intro p q hpq
  rw [root, Matrix.single_apply, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  exact (not_le_of_gt Fin.castSucc_lt_succ) hpq

private theorem root_frequency (a : ℂˣ) (i : Fin r) (t : ℝ) :
    complexWhittakerFrequency a (root i ((a⁻¹ : ℂˣ) * (t : ℂ))) =
      (4 * Real.pi * t : ℝ) * Complex.I := by
  have hsum : ∑ j : Fin r, root i ((a⁻¹ : ℂˣ) * (t : ℂ)) j.castSucc j.succ =
      (a⁻¹ : ℂˣ) * (t : ℂ) := by
    rw [Finset.sum_eq_single i]
    · simp [root]
    · intro j _ hji
      rw [root, Matrix.single_apply, ite_eq_right]
      exact fun h => hji ((Fin.castSucc_injective _ h.1).symm)
    · simp
  rw [complexWhittakerFrequency, hsum, ← mul_assoc, Units.mul_inv, one_mul,
    Algebra.trace_complex_apply, Complex.ofReal_re]
  push_cast
  ring

private def rootRatio (y : Fin (r + 1) → ℝ) (i : Fin r) : ℝ :=
  Real.exp (y i.castSucc - y i.succ)

private def rootDirection (a : ℂˣ) (i : Fin r) (k : K) : Mat :=
  ((k : G)⁻¹).val * root i (a⁻¹ : ℂˣ) * (k : G).val

private theorem torus_conj_root (a : ℂˣ) (i : Fin r) (y : Fin (r + 1) → ℝ) :
    (logTorus y).val * root i (a⁻¹ : ℂˣ) * (logTorus y)⁻¹.val =
      root i ((a⁻¹ : ℂˣ) * (rootRatio y i : ℂ)) := by
  ext p q
  rw [logTorus_val, logTorus_inv_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [root, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [rootRatio, sub_eq_add_neg, Real.exp_add, Complex.ofReal_mul]
    ring
  · simp

private theorem root_derivative_norm (W : V) (i : Fin r) (y : Fin (r + 1) → ℝ) (k : K) :
    ‖(R (rootDirection a i k) W).val (logTorus y * (k : G))‖ =
      (4 * Real.pi * rootRatio y i) * ‖W.val (logTorus y * (k : G))‖ := by
  let b := logTorus y
  let Z := root i ((a⁻¹ : ℂˣ) * (rootRatio y i : ℂ))
  have hconj : ((b * (k : G))⁻¹).val * Z * (b * (k : G)).val =
      rootDirection a i k := by
    rw [show Z = b.val * root i (a⁻¹ : ℂˣ) * b⁻¹.val from (torus_conj_root a i y).symm,
      mul_inv_rev, Units.val_mul, Units.val_mul]
    calc
      _ = ((k : G)⁻¹).val * (b⁻¹.val * b.val) * root i (a⁻¹ : ℂˣ) *
          (b⁻¹.val * b.val) * (k : G).val := by simp only [mul_assoc]
      _ = _ := by rw [show b⁻¹.val * b.val = 1 from b.inv_val]; simp [rootDirection]
  have h := complexWhittakerModel_unipotent_derivative W.2 (b * (k : G)) Z
    (root_strictUpper i _)
  rw [hconj] at h
  change ‖rightDerivative (matrixModel ℂ (r + 1)) (rootDirection a i k) W.val
      (b * (k : G))‖ = _
  rw [h, show complexWhittakerFrequency a Z = (4 * Real.pi * rootRatio y i : ℝ) * Complex.I
    from root_frequency a i _]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    abs_of_nonneg]
  exact mul_nonneg (by positivity) (Real.exp_pos _).le

private def directionMap (W : V) : Mat →ₗ[ℝ] V where
  toFun X := R X W
  map_add' X Y := Subtype.ext (rightDerivative_add_left X Y W.val)
  map_smul' c X := Subtype.ext (rightDerivative_smul_left c X W.val)

private theorem exists_root_derivative_bound (i : Fin r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : V) (k : K) (g : G),
      ‖(R (rootDirection a i k) W).val g‖ ≤ C *
        ∑ j, ‖(R (Module.Free.chooseBasis ℝ Mat j) W).val g‖ := by
  let b := Module.Free.chooseBasis ℝ Mat
  have hdir : Continuous (rootDirection a i) :=
    (((Units.continuous_val.comp continuous_subtype_val.inv).mul continuous_const).mul
      (Units.continuous_val.comp continuous_subtype_val))
  have hb : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ k : K, ‖b.repr (rootDirection a i k) j‖ ≤ B := by
    intro j
    have hc : Continuous (fun k : K => ‖b.repr (rootDirection a i k) j‖) :=
      ((b.coord j).continuous_of_finiteDimensional.comp hdir).norm
    obtain ⟨B, hB⟩ := (isCompact_range hc).bddAbove
    exact ⟨max 0 B, le_max_left _ _, fun k =>
      (hB (Set.mem_range_self k)).trans (le_max_right _ _)⟩
  choose B hB0 hB using hb
  refine ⟨∑ j, B j, Finset.sum_nonneg fun j _ => hB0 j, fun W k g => ?_⟩
  have he : R (rootDirection a i k) W =
      ∑ j, b.repr (rootDirection a i k) j • R (b j) W := by
    change directionMap W (rootDirection a i k) =
      ∑ j, b.repr (rootDirection a i k) j • directionMap W (b j)
    simp_rw [← map_smul]
    rw [← map_sum, b.sum_repr]
  rw [he, Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  change ‖b.repr (rootDirection a i k) j • (R (b j) W).val g‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right ((hB j k).trans
    (Finset.single_le_sum (fun i _ => hB0 i) (Finset.mem_univ j))) (norm_nonneg _)

private def derivativeWord (Xs : List Mat) (W : V) : V :=
  (Xs.map R).prod W

private theorem exists_list_moment_bound (W : V) {N : ℕ}
    (hN : ∀ Xs : List Mat, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G,
      ‖(derivativeWord Xs W).val g‖ ≤ C * max 1 (complexMatrixHeight g) ^ N)
    (rs : List (Fin r)) (Xs : List Mat) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin (r + 1) → ℝ) (k : K),
      let g := logTorus y * (k : G)
      ‖(derivativeWord Xs W).val g‖ * (rs.map fun i => max 1 (rootRatio y i)).prod ≤
        C * max 1 (complexMatrixHeight g) ^ N := by
  induction rs generalizing Xs with
  | nil =>
    obtain ⟨C, hC0, hC⟩ := hN Xs
    exact ⟨C, hC0, fun y k => by simpa using hC (logTorus y * (k : G))⟩
  | cons i rs ih =>
    let b := Module.Free.chooseBasis ℝ Mat
    obtain ⟨A, hA0, hA⟩ := exists_root_derivative_bound (ds := ds) (a := a) i
    obtain ⟨C, hC0, hC⟩ := ih Xs
    choose B hB0 hB using fun j : Module.Free.ChooseBasisIndex ℝ Mat => ih (b j :: Xs)
    have hp : 0 < 4 * Real.pi := by positivity
    have hAπ := div_nonneg hA0 hp.le
    refine ⟨C + (A / (4 * Real.pi)) * (∑ j, B j),
      add_nonneg hC0 (mul_nonneg hAπ (Finset.sum_nonneg fun j _ => hB0 j)), fun y k => ?_⟩
    let g := logTorus y * (k : G)
    let H := max 1 (complexMatrixHeight g) ^ N
    let m := (rs.map fun j => max 1 (rootRatio y j)).prod
    let f := derivativeWord Xs W
    let S := ∑ j, ‖(R (b j) f).val g‖
    have hm : 0 ≤ m := List.prod_nonneg fun t ht => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
      exact zero_le_one.trans (le_max_left _ _)
    have hratio : 0 ≤ rootRatio y i := (Real.exp_pos _).le
    have hmax : max 1 (rootRatio y i) ≤ 1 + rootRatio y i :=
      max_le (le_add_of_nonneg_right hratio) (le_add_of_nonneg_left zero_le_one)
    have hstep : rootRatio y i * ‖f.val g‖ ≤ (A * S) / (4 * Real.pi) := by
      apply (le_div_iff₀ hp).mpr
      calc
        _ = (4 * Real.pi * rootRatio y i) * ‖f.val g‖ := by ring
        _ ≤ A * S := (root_derivative_norm f i y k).symm.trans_le (hA f k g)
    have hsum : (∑ j, ‖(R (b j) f).val g‖ * m) ≤ (∑ j, B j) * H := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => hB j y k
    change ‖f.val g‖ * (max 1 (rootRatio y i) * m) ≤
      (C + (A / (4 * Real.pi)) * (∑ j, B j)) * H
    calc
      _ ≤ ‖f.val g‖ * ((1 + rootRatio y i) * m) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmax hm) (norm_nonneg _)
      _ = ‖f.val g‖ * m + (rootRatio y i * ‖f.val g‖) * m := by ring
      _ ≤ C * H + ((A * S) / (4 * Real.pi)) * m :=
        add_le_add (hC y k) (mul_le_mul_of_nonneg_right hstep hm)
      _ = C * H + (A / (4 * Real.pi)) * (∑ j, ‖(R (b j) f).val g‖ * m) := by
        rw [← Finset.sum_mul]
        dsimp only [S]
        ring
      _ ≤ C * H + (A / (4 * Real.pi)) * ((∑ j, B j) * H) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hAπ)
      _ = _ := by ring

private theorem exists_repeated_roots (M : ℕ) :
    ∃ rs : List (Fin r), ∀ v : Fin r → ℝ, (rs.map v).prod = ∏ i, v i ^ M := by
  refine ⟨(List.ofFn fun i : Fin r => List.replicate M i).flatten, ?_⟩
  intro v
  rw [List.map_flatten, List.prod_flatten, List.map_ofFn, List.map_ofFn, List.prod_ofFn]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [List.map_replicate, List.prod_replicate]

private theorem rootRatio_clamp (y : Fin (r + 1) → ℝ) (i : Fin r) :
    max 1 (rootRatio y i) = Real.exp (max (y i.castSucc - y i.succ) 0) := by
  rw [rootRatio, Real.exp_monotone.map_max, Real.exp_zero, max_comm]

private theorem exists_diagonal_moment (W : V) :
    ∃ N : ℕ, ∀ (M : ℕ) (Xs : List Mat), ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin (r + 1) → ℝ) (k : K),
      let g := logTorus y * (k : G)
      ‖(derivativeWord Xs W).val g‖ *
          Real.exp ((M : ℝ) * ∑ i : Fin r, max (y i.castSucc - y i.succ) 0) ≤
        C * max 1 (complexMatrixHeight g) ^ N := by
  obtain ⟨N, hN⟩ := complexWhittakerUniformDerivativeGrowth r ds a W
  refine ⟨N, fun M Xs => ?_⟩
  obtain ⟨rs, hrs⟩ := exists_repeated_roots (r := r) M
  obtain ⟨C, hC0, hC⟩ := exists_list_moment_bound W hN rs Xs
  refine ⟨C, hC0, fun y k => ?_⟩
  have h := hC y k
  dsimp only at h ⊢
  rw [hrs] at h
  rw [Finset.mul_sum, Real.exp_sum]
  simpa only [rootRatio_clamp, ← Real.exp_nat_mul] using h

end RootDerivative

/-- A bound for the matrix height in logarithmic Iwasawa coordinates. -/
theorem height_logTorus_mul_le {n : ℕ} (y : Fin n → ℝ) (k : unitaryCompact ℂ n) :
    max 1 (complexMatrixHeight (logTorus y * (k : Langlands.GeneralLinear n ℂ))) ≤
      (1 + 2 * (n : ℝ) ^ 2) * Real.exp (2 * ∑ j, |y j|) := by
  let G := Langlands.GeneralLinear n ℂ
  let S := ∑ j, |y j|
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hy (j : Fin n) : |y j| ≤ S :=
    Finset.single_le_sum (fun j _ => abs_nonneg (y j)) (Finset.mem_univ j)
  have hterm {c : ℂ} {t : ℝ} (hc : ‖c‖ ≤ 1) (ht : t ≤ S) :
      ‖(Real.exp t : ℂ) * c‖ ^ 2 ≤ Real.exp (2 * S) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ Real.exp S ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        calc
          Real.exp t * ‖c‖ ≤ Real.exp t * 1 :=
            mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
          _ ≤ Real.exp S := by simpa only [mul_one] using Real.exp_monotone ht
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hK (κ : unitaryCompact ℂ n) (p q : Fin n) : ‖(κ : G).val p q‖ ≤ 1 :=
    LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup κ.2 p q
  have hbound : complexMatrixHeight (logTorus y * (k : G)) ≤
      2 * (n : ℝ) ^ 2 * Real.exp (2 * S) := by
    unfold complexMatrixHeight
    calc
      _ ≤ ∑ _p : Fin n, ∑ _q : Fin n, 2 * Real.exp (2 * S) := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
        rw [two_mul, Units.val_mul, logTorus_val, Matrix.diagonal_mul,
          mul_inv_rev, Units.val_mul, logTorus_inv_val, Matrix.mul_diagonal]
        exact add_le_add (hterm (hK k p q) ((le_abs_self _).trans (hy p)))
          (by rw [mul_comm]; exact hterm (hK k⁻¹ p q) ((neg_le_abs _).trans (hy q)))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  rw [add_mul, one_mul]
  apply max_le
  · calc
      1 ≤ Real.exp (2 * S) := Real.one_le_exp_iff.mpr (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · exact hbound.trans (le_add_of_nonneg_left (Real.exp_nonneg _))

end ComplexLocalWhittakerGauge

open ComplexLocalWhittakerGauge

/-- At a positive diagonal times a unitary matrix, every derivative word of a fixed complex
Whittaker vector has arbitrarily rapid decay in the positive simple-root logarithms.
One exponential growth coefficient for the sum of the absolute toral logarithms works for
every word and decay order. -/
def ComplexWhittakerSimpleRootMajorizationStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ) (W : complexWhittakerModel r ds a),
    ∃ N : ℕ, ∀ (M : ℕ) (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℂ (r + 1)),
        ‖((Xs.map (complexWhittakerRightDerivative r ds a)).prod W).val
            (logTorus y * (k : Langlands.GeneralLinear (r + 1) ℂ))‖ ≤
          C * Real.exp ((N : ℝ) * ∑ j, |y j| -
            (M : ℝ) * ∑ i : Fin r, max (y i.castSucc - y i.succ) 0)

theorem complexWhittakerSimpleRootMajorization : ComplexWhittakerSimpleRootMajorizationStatement := by
  intro r ds a W
  obtain ⟨N, hN⟩ := exists_diagonal_moment W
  let A : ℝ := 1 + 2 * (((r + 1 : ℕ) : ℝ) ^ 2)
  refine ⟨2 * N, fun M Xs => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hN M Xs
  refine ⟨C * A ^ N, mul_nonneg hC0 (pow_nonneg (by dsimp [A]; positivity) _), fun y k => ?_⟩
  have h := (hC y k).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (height_logTorus_mul_le y k) N) hC0)
  rw [mul_pow, ← mul_assoc, ← Real.exp_nat_mul] at h
  have hexp : (N : ℝ) * (2 * ∑ j, |y j|) = ((2 * N : ℕ) : ℝ) * ∑ j, |y j| := by
    push_cast
    ring
  rw [hexp] at h
  rw [Real.exp_sub, ← mul_div_assoc]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr h

end Langlands.Global.RankinSelbergGlobal
