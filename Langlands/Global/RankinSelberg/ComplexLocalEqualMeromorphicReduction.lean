import Langlands.Global.RankinSelberg.ComplexLocalEqualConvergenceReduction
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerWordGrowth

/-! # The complex equal-rank local equation reduced to meromorphic premises -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open ComplexCharacterChange (complexMatrixHeight_mul_le)
open ComplexLocalConvergence

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "M" => Matrix I I ℂ
local notation "K" => unitaryCompact ℂ n

private theorem coord_le_positiveLogSum (x : I → ℝ) (i : I) : x i ≤ positiveLogSum x :=
  (le_max_left _ _).trans (Finset.single_le_sum
    (f := fun i => max (x i) 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ i))

private theorem expDiagonal_entry_norm_sq_le (x : I → ℝ) (T : ℝ) (hT : ∀ i, x i ≤ T)
    (i j : I) : ‖(expDiagonal x).val i j‖ ^ 2 ≤ Real.exp (2 * T) := by
  rw [expDiagonal_val]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
      pow_two, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hT i])
  · rw [Matrix.diagonal_apply_ne _ hij, norm_zero, zero_pow (by decide)]
    exact Real.exp_nonneg _

private theorem expDiagonal_height_le (x : I → ℝ) :
    complexMatrixHeight (expDiagonal x) ≤
      (2 * (n : ℝ) ^ 2) * Real.exp (2 * (positiveLogSum x + positiveLogSum (-x))) := by
  let T := positiveLogSum x + positiveLogSum (-x)
  have hn (y : I → ℝ) : 0 ≤ positiveLogSum y := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hpos i : x i ≤ T :=
    (coord_le_positiveLogSum x i).trans (le_add_of_nonneg_right (hn _))
  have hneg i : (-x) i ≤ T :=
    (coord_le_positiveLogSum (-x) i).trans (le_add_of_nonneg_left (hn _))
  unfold complexMatrixHeight
  rw [← expDiagonal_neg]
  calc
    _ ≤ ∑ _i : I, ∑ _j : I, (Real.exp (2 * T) + Real.exp (2 * T)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        add_le_add (expDiagonal_entry_norm_sq_le x T hpos i j)
          (expDiagonal_entry_norm_sq_le (-x) T hneg i j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one, T]
      ring

private theorem exists_torus_height_bound :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (x : I → ℝ) (k : K),
      complexMatrixHeight (expDiagonal x * k.val) ≤
        H * Real.exp (2 * (positiveLogSum x + positiveLogSum (-x))) := by
  have hc : Continuous (fun k : K => complexMatrixHeight k.val) :=
    continuous_complexMatrixHeight.comp continuous_subtype_val
  obtain ⟨C, hC⟩ := (isCompact_univ (X := K)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨(2 * (n : ℝ) ^ 2) * max C 0, by positivity, fun x k => ?_⟩
  have hk0 : 0 ≤ complexMatrixHeight k.val :=
    (by norm_num : (0 : ℝ) ≤ 2).trans (ComplexPlaceAnalytic.two_le_complexMatrixHeight (by omega) _)
  have hk := hC k (Set.mem_univ _)
  rw [Real.norm_of_nonneg hk0] at hk
  calc
    _ ≤ complexMatrixHeight (expDiagonal x) * complexMatrixHeight k.val :=
      complexMatrixHeight_mul_le _ _
    _ ≤ ((2 * (n : ℝ) ^ 2) * Real.exp (2 * (positiveLogSum x + positiveLogSum (-x)))) *
        max C 0 :=
      mul_le_mul (expDiagonal_height_le x) (hk.trans (le_max_left _ _)) hk0 (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 500000 in
private theorem exists_simpleRoot_conjugate_bound (a : ℂˣ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (i : Fin r) (k : K),
      ‖(k.val⁻¹).val * simpleRootDirection a i * k.val.val‖ ≤ D := by
  have hv : Continuous (fun k : K => k.val.val) := Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous (fun k : K => (k.val⁻¹).val) :=
    Units.continuous_val.comp (continuous_inv.comp continuous_subtype_val)
  let Y (p : Fin r × K) : M := (p.2.val⁻¹).val * simpleRootDirection a p.1 * p.2.val.val
  have hd : Continuous (simpleRootDirection a : Fin r → M) := continuous_of_discreteTopology
  have hY : Continuous Y := ((hi.comp continuous_snd).mul
    (hd.comp continuous_fst)).mul (hv.comp continuous_snd)
  obtain ⟨D, hD⟩ := (isCompact_univ (X := Fin r × K)).exists_bound_of_continuousOn hY.continuousOn
  exact ⟨max D 0, le_max_right _ _, fun i k => (hD (i, k) (Set.mem_univ _)).trans (le_max_left _ _)⟩

/-- The Whittaker intertwiner model has one growth exponent for every word
of the conjugated simple-root derivatives of a fixed inducing vector. -/
theorem complexLocalWhittakerUniformGrowth : ComplexLocalWhittakerUniformGrowthStatement := by
  intro r ds _ a B hB f
  obtain ⟨D, hD, hdir⟩ := exists_simpleRoot_conjugate_bound (r := r) a
  obtain ⟨N, C, hC, hword⟩ := exists_complexWhittaker_right_word_growth hB f hD
  obtain ⟨H, hH, hheight⟩ := exists_torus_height_bound (r := r)
  refine ⟨2 * (N : ℝ), by positivity, fun word => ?_⟩
  refine ⟨C word.length * H ^ N, mul_nonneg (hC _) (pow_nonneg hH _), fun x k => ?_⟩
  let Y (i : Fin r) := (k.val⁻¹).val * simpleRootDirection a i * k.val.val
  let g := expDiagonal x * k.val
  let T := positiveLogSum x + positiveLogSum (-x)
  have hY (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hX : X ∈ word.map Y) : ‖X‖ ≤ D := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact hdir i k
  have hg : 0 ≤ complexMatrixHeight g :=
    (by norm_num : (0 : ℝ) ≤ 2).trans (ComplexPlaceAnalytic.two_le_complexMatrixHeight (by omega) g)
  calc
    _ ≤ C word.length * complexMatrixHeight g ^ N := by
      simpa only [simpleRootStandardWord, Y, List.length_map] using hword (word.map Y) hY g
    _ ≤ C word.length * (H * Real.exp (2 * T)) ^ N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg (hheight x k) _) (hC _)
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul, mul_assoc]
      rw [show (N : ℝ) * (2 * T) = 2 * (N : ℝ) * T by ring]

/-- The higher-rank analytic work remaining in the local equal-rank equation
consists of meromorphic continuation and the identity of the continuations. -/
def ComplexLocalEqualMeromorphicReductionStatement : Prop :=
  ComplexLocalEqualPrimalContinuationStatement →
    ComplexLocalEqualMeromorphicEquationStatement →
      ComplexLocalEqualFunctionalEquationStatement

theorem complexLocalEqualMeromorphicReduction : ComplexLocalEqualMeromorphicReductionStatement :=
  complexLocalEqualConvergenceReduction complexLocalWhittakerUniformGrowth

end Langlands.Global.RankinSelbergGlobal
