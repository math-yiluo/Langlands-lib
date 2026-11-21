import Langlands.Global.RankinSelberg.ComplexGodementCompactPairing
import Langlands.Global.RankinSelberg.ComplexJacquetChamberNonzero

/-! # Central polynomial weights with arbitrarily small displacement moment -/

noncomputable section

open Set MeasureTheory
open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexCentralPolynomialWeight

open Langlands.Archimedean.UnitaryFinitePolynomial (coord polynomialStar)
open ComplexGodement (compactMatrixHaar)
open ComplexJacquetChamberNonzero (exists_pos_integral_pow_of_peak)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℂ

local instance centralWeightMeasurable (n : ℕ) : MeasurableSpace (K n) := borel _
local instance centralWeightBorel (n : ℕ) : BorelSpace (K n) := ⟨rfl⟩

variable {n : ℕ}

private def entryDifference (i j : Fin n) : C(K n, ℂ) :=
  coord n (Sum.inl (i, j)) - algebraMap ℂ C(K n, ℂ) ((1 : Mat n) i j)

private theorem entryDifference_apply (i j : Fin n) (k : K n) :
    entryDifference i j k = (k.val - 1) i j := rfl

private def squareDisplacement (n : ℕ) : C(K n, ℂ) :=
  ∑ i : Fin n, ∑ j : Fin n, entryDifference i j * star (entryDifference i j)

private theorem squareDisplacement_polynomial (n : ℕ) : squareDisplacement n ∈ polynomialStar n := by
  have he (i j : Fin n) : entryDifference i j ∈ polynomialStar n :=
    sub_mem (StarAlgebra.subset_adjoin ℂ _ ⟨(i, j), rfl⟩) (Subalgebra.algebraMap_mem _ _)
  have hm (i j : Fin n) : entryDifference i j * star (entryDifference i j) ∈ polynomialStar n :=
    mul_mem (he i j) (star_mem (he i j))
  exact Submodule.sum_mem (polynomialStar n).toSubalgebra.toSubmodule fun i _ =>
    Submodule.sum_mem (polynomialStar n).toSubalgebra.toSubmodule fun j _ => hm i j

private def displacementSquared (k : K n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ‖(k.val - 1) i j‖ ^ 2

private theorem squareDisplacement_apply (k : K n) : squareDisplacement n k = (displacementSquared k : ℂ) := by
  simp only [squareDisplacement, ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply,
    entryDifference_apply, displacementSquared, Complex.ofReal_sum, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

private theorem displacementSquared_nonneg (k : K n) : 0 ≤ displacementSquared k :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem displacementSquared_eq_zero (k : K n) : displacementSquared k = 0 ↔ k = 1 := by
  constructor
  · intro h
    apply Matrix.UnitaryGroup.ext
    intro i j
    have hr := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg ‖(k.val - 1) i j‖)).mp h i (Finset.mem_univ _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖(k.val - 1) i j‖)).mp hr j
      (Finset.mem_univ _)
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hij))
  · rintro rfl
    simp [displacementSquared]

private theorem continuous_displacementSquared (n : ℕ) : Continuous (displacementSquared (n := n)) := by
  have h := Complex.continuous_re.comp (squareDisplacement n).continuous
  simpa only [Function.comp_def, squareDisplacement_apply, Complex.ofReal_re] using h

private theorem displacementSquared_trace (k : K n) :
    (displacementSquared k : ℂ) = Matrix.trace ((k.val - 1) * star (k.val - 1)) := by
  simp only [displacementSquared, Complex.ofReal_sum, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem displacementSquared_conj (g k : K n) : displacementSquared (g * k * g⁻¹) = displacementSquared k := by
  apply Complex.ofReal_injective
  rw [displacementSquared_trace, displacementSquared_trace]
  let v := g.val
  let u := g⁻¹.val
  let A := k.val - 1
  have huv : u * v = 1 := congrArg Subtype.val (inv_mul_cancel g)
  have hvu : v * u = 1 := congrArg Subtype.val (mul_inv_cancel g)
  have hsv : star v = u := (Matrix.UnitaryGroup.inv_val g).symm
  have hsu : star u = v := by rw [← hsv, star_star]
  have he : (g * k * g⁻¹ : K n).val - 1 = v * A * u := by
    change v * k.val * u - 1 = v * (k.val - 1) * u
    rw [mul_sub, sub_mul, mul_one, hvu]
  rw [he, star_mul, star_mul, hsu, hsv, ← mul_assoc v (star A) u]
  have hp : (v * A * u) * (v * star A * u) = v * (A * star A) * u := by
    rw [← mul_assoc (v * A * u) (v * star A) u, ← mul_assoc (v * A * u) v (star A),
      mul_assoc (v * A) u v, huv, mul_one, mul_assoc v A (star A)]
  rw [hp, Matrix.trace_mul_cycle, huv, one_mul]

private theorem continuous_displacement (n : ℕ) : Continuous fun k : K n => ‖k.val - 1‖ :=
  (continuous_subtype_val.sub continuous_const).norm

private theorem exists_positive_peak (n : ℕ) :
    ∃ (q : K n → ℝ) (Q : C(K n, ℂ)), Q ∈ polynomialStar n ∧ Continuous q ∧
    (∀ k, Q k = (q k : ℂ)) ∧ (∀ k, 0 ≤ q k) ∧ (∀ k, q k ≤ 1) ∧
    (∀ k, q k = 1 ↔ k = 1) ∧ ∀ g k, q (g * k * g⁻¹) = q k := by
  obtain ⟨B, hB⟩ := (isCompact_range (continuous_displacementSquared n)).bddAbove
  let C := max 0 B + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hd (k : K n) : displacementSquared k ≤ C :=
    (hB (mem_range_self k)).trans ((le_max_right 0 B).trans (le_add_of_nonneg_right zero_le_one))
  let q (k : K n) := 1 - C⁻¹ * displacementSquared k
  let Q : C(K n, ℂ) := 1 - ((C⁻¹ : ℝ) : ℂ) • squareDisplacement n
  have hQ : Q ∈ polynomialStar n := sub_mem (one_mem _)
    ((polynomialStar n).toSubalgebra.smul_mem (squareDisplacement_polynomial n) _)
  refine ⟨q, Q, hQ, continuous_const.sub (continuous_const.mul (continuous_displacementSquared n)),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    simp [Q, q, squareDisplacement_apply, smul_eq_mul]
  · intro k
    dsimp only [q]
    exact sub_nonneg.mpr ((mul_le_mul_of_nonneg_left (hd k) (inv_nonneg.mpr hC.le)).trans_eq
      (inv_mul_cancel₀ hC.ne'))
  · intro k
    exact sub_le_self _ (mul_nonneg (inv_nonneg.mpr hC.le) (displacementSquared_nonneg k))
  · intro k
    change 1 - C⁻¹ * displacementSquared k = 1 ↔ k = 1
    rw [sub_eq_self, mul_eq_zero, or_iff_right (inv_ne_zero hC.ne'), displacementSquared_eq_zero]
  · intro g k
    simp only [q, displacementSquared_conj]

/-- Positive central polynomial weights of unit mass can have arbitrarily small first moment
of displacement in the matrix operator norm. -/
def ComplexCentralPolynomialWeightStatement : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ (w : C(K n, ℂ)) (W : K n → ℝ),
    w ∈ polynomialStar n ∧ Continuous W ∧ (∀ k, 0 ≤ W k) ∧
    (∀ k, w k = (W k : ℂ)) ∧ (∀ g k, w (g * k * g⁻¹) = w k) ∧
    (∫ k, W k ∂compactMatrixHaar n) = 1 ∧
    (∫ k, W k * ‖k.val - 1‖ ∂compactMatrixHaar n) < ε

set_option maxHeartbeats 700000 in
theorem complexCentralPolynomialWeight : ComplexCentralPolynomialWeightStatement := by
  intro n ε hε
  let μ := compactMatrixHaar n
  obtain ⟨q, Q, hQ, hqc, hqQ, hq₀, hq₁, hqeq, hqconj⟩ := exists_positive_peak n
  have hqOne : q 1 = 1 := (hqeq 1).mpr rfl
  have hpeak (U : Set (K n)) (hU : IsOpen U) (h1 : 1 ∈ U) :
      ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ k ∉ U, q k ≤ c := by
    by_cases h : Uᶜ.Nonempty
    · obtain ⟨u, hu, hMax⟩ := hU.isClosed_compl.isCompact.exists_isMaxOn h hqc.continuousOn
      refine ⟨q u, hq₀ u, lt_of_le_of_ne (hq₁ u) (fun hh => hu ((hqeq u).mp hh ▸ h1)), ?_⟩
      exact fun k hk => hMax hk
    · exact ⟨0, le_rfl, zero_lt_one, fun k hk => (h ⟨k, hk⟩).elim⟩
  let d (k : K n) := ‖k.val - 1‖
  have hd : Continuous d := continuous_displacement n
  let F (k : K n) : ℂ := ((1 - ε⁻¹ * d k : ℝ) : ℂ)
  have hF : Continuous F := Complex.continuous_ofReal.comp (continuous_const.sub (continuous_const.mul hd))
  have hF₁ : F 1 = 1 := by simp [F, d]
  have hInt {V : Type} [NormedAddCommGroup V] {f : K n → V} (hf : Continuous f) : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨j, hj⟩ := exists_pos_integral_pow_of_peak μ hF (hInt hF) hF₁ hqc hq₀ hq₁ hqOne hpeak
  let Z : ℝ := ∫ k, q k ^ j ∂μ
  have hZ : 0 < Z := (hqc.pow j).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun k => pow_nonneg (hq₀ k) _) (x := (1 : K n)) (by simp [hqOne])
  let W (k : K n) := Z⁻¹ * q k ^ j
  let w : C(K n, ℂ) := ((Z⁻¹ : ℝ) : ℂ) • Q ^ j
  have hW : Continuous W := continuous_const.mul (hqc.pow _)
  have hw (k : K n) : w k = (W k : ℂ) := by
    simp only [w, W, ContinuousMap.smul_apply, ContinuousMap.pow_apply, hqQ, smul_eq_mul, Complex.ofReal_mul,
      Complex.ofReal_pow]
  refine ⟨w, W, (polynomialStar n).toSubalgebra.smul_mem (pow_mem hQ _) _, hW,
    fun k => mul_nonneg (inv_nonneg.mpr hZ.le) (pow_nonneg (hq₀ k) _), hw,
    fun g k => by rw [hw, hw]; simp only [W, hqconj], ?_, ?_⟩
  · change ∫ k, Z⁻¹ * q k ^ j ∂μ = 1
    rw [integral_const_mul, inv_mul_cancel₀ hZ.ne']
  · have hm : (∫ k, d k * q k ^ j ∂μ) < ε * Z := by
      have he : (fun k => F k * (q k : ℂ) ^ j) =
          fun k => (((1 - ε⁻¹ * d k) * q k ^ j : ℝ) : ℂ) := by
        funext k
        simp only [F, Complex.ofReal_mul, Complex.ofReal_pow]
      rw [he, integral_complex_ofReal, Complex.ofReal_re] at hj
      have hFun : (fun k => (1 - ε⁻¹ * d k) * q k ^ j) =
          fun k => q k ^ j - ε⁻¹ * (d k * q k ^ j) := funext fun k => by ring
      have hqInt : Integrable (fun k => q k ^ j) μ := hInt (hqc.pow j)
      have hdInt : Integrable (fun k => ε⁻¹ * (d k * q k ^ j)) μ :=
        hInt (continuous_const.mul (hd.mul (hqc.pow j)))
      rw [hFun, integral_sub hqInt hdInt, integral_const_mul, ← div_eq_inv_mul, sub_pos] at hj
      exact (div_lt_iff₀ hε).mp hj |>.trans_eq (mul_comm _ _)
    have he : (fun k => W k * ‖k.val - 1‖) = fun k => Z⁻¹ * (d k * q k ^ j) :=
      funext fun k => by change Z⁻¹ * q k ^ j * d k = _; ring
    change (∫ k, W k * ‖k.val - 1‖ ∂μ) < ε
    rw [he, integral_const_mul, ← div_eq_inv_mul]
    exact (div_lt_iff₀ hZ).mpr hm

end Langlands.Global.RankinSelbergGlobal.ComplexCentralPolynomialWeight
