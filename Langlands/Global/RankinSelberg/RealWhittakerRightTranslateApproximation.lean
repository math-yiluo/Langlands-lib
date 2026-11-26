import Langlands.Global.RankinSelberg.RealExactStandardEvaluation
import Langlands.Global.RankinSelberg.ComplexJacquetChamberNonzero

/-! # Positive compact approximation of real Whittaker right translates -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealWhittakerRightTranslateApproximation

open Langlands.Archimedean (unitaryCompact unitaryCompactMatrix continuous_unitaryCompactMatrix)
open Langlands.Archimedean.OrthogonalFinitePolynomial (entry entry_apply polynomialStar)
open Langlands.Archimedean.RealPrincipalSeriesDuality (haarK)
open Langlands.LocalFactor.Archimedean (RealBlock)
open ComplexJacquetChamberNonzero (exists_pos_integral_pow_of_peak)
open RealExactStandardEvaluation (compactWeight finiteDimensional_compactWeight)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "Kc" => fun n => unitaryCompact ℝ n
local notation "Std" => Automorphic.realStandardKFinite

local instance rightTranslateApproximationMeasurable (j : ℕ) :
    MeasurableSpace (unitaryCompact ℝ j) := borel _
local instance rightTranslateApproximationBorel (j : ℕ) :
    BorelSpace (unitaryCompact ℝ j) := ⟨rfl⟩

variable {n : ℕ}

/-! ## A polynomial peak at the identity -/

/-- The sum of squared entry displacements of an orthogonal matrix from the identity. -/
def displacementSquared (k : Kc n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ((k.val : Matrix (Fin n) (Fin n) ℝ) i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j) ^ 2

private def entryDifference (n : ℕ) (i j : Fin n) : C(Matrix.unitaryGroup (Fin n) ℝ, ℂ) :=
  entry n (i, j) - algebraMap ℂ C(Matrix.unitaryGroup (Fin n) ℝ, ℂ)
    (((1 : Matrix (Fin n) (Fin n) ℝ) i j : ℝ) : ℂ)

private def squareDisplacement (n : ℕ) : C(Matrix.unitaryGroup (Fin n) ℝ, ℂ) :=
  ∑ i : Fin n, ∑ j : Fin n, entryDifference n i j * entryDifference n i j

private theorem squareDisplacement_polynomial (n : ℕ) : squareDisplacement n ∈ polynomialStar n := by
  have he (i j : Fin n) : entryDifference n i j ∈ polynomialStar n :=
    sub_mem (StarAlgebra.subset_adjoin ℂ _ ⟨(i, j), rfl⟩) (Subalgebra.algebraMap_mem _ _)
  exact Submodule.sum_mem (polynomialStar n).toSubalgebra.toSubmodule fun i _ =>
    Submodule.sum_mem (polynomialStar n).toSubalgebra.toSubmodule fun j _ =>
      (polynomialStar n).mul_mem (he i j) (he i j)

private theorem squareDisplacement_apply (k : Kc n) :
    squareDisplacement n (unitaryCompactMatrix ℝ n k) = (displacementSquared k : ℂ) := by
  simp only [squareDisplacement, entryDifference, displacementSquared, ContinuousMap.sum_apply,
    ContinuousMap.mul_apply, ContinuousMap.sub_apply, _root_.algebraMap_apply, entry_apply,
    smul_eq_mul, mul_one]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sq]
  rfl

theorem displacementSquared_nonneg (k : Kc n) : 0 ≤ displacementSquared k :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem displacementSquared_eq_zero (k : Kc n) : displacementSquared k = 0 ↔ k = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    apply Units.ext
    funext i j
    have hr := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg
        ((k.val : Matrix (Fin n) (Fin n) ℝ) i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j))).mp h i
      (Finset.mem_univ _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg
      ((k.val : Matrix (Fin n) (Fin n) ℝ) i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j))).mp hr j
      (Finset.mem_univ _)
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hij)
  · rintro rfl
    simp [displacementSquared]

theorem continuous_displacementSquared (n : ℕ) :
    Continuous (displacementSquared (n := n)) := by
  unfold displacementSquared
  fun_prop

theorem continuous_displacement (n : ℕ) :
    Continuous fun k : Kc n => ‖(k.val : Matrix (Fin n) (Fin n) ℝ) - 1‖ :=
  ((Units.continuous_val.comp continuous_subtype_val).sub continuous_const).norm

private theorem exists_positive_peak (n : ℕ) :
    ∃ (q : Kc n → ℝ) (Q : C(Matrix.unitaryGroup (Fin n) ℝ, ℂ)), Q ∈ polynomialStar n ∧
      Continuous q ∧ (∀ k, Q (unitaryCompactMatrix ℝ n k) = (q k : ℂ)) ∧ (∀ k, 0 ≤ q k) ∧
      (∀ k, q k ≤ 1) ∧ (∀ k, q k = 1 ↔ k = 1) := by
  obtain ⟨B, hB⟩ := (isCompact_range (continuous_displacementSquared n)).bddAbove
  let C := max 0 B + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hd (k : Kc n) : displacementSquared k ≤ C :=
    (hB (mem_range_self k)).trans ((le_max_right 0 B).trans (le_add_of_nonneg_right zero_le_one))
  let q (k : Kc n) := 1 - C⁻¹ * displacementSquared k
  let Q : C(Matrix.unitaryGroup (Fin n) ℝ, ℂ) := 1 - ((C⁻¹ : ℝ) : ℂ) • squareDisplacement n
  have hQ : Q ∈ polynomialStar n := sub_mem (one_mem _)
    ((polynomialStar n).toSubalgebra.smul_mem (squareDisplacement_polynomial n) _)
  refine ⟨q, Q, hQ, continuous_const.sub (continuous_const.mul (continuous_displacementSquared n)),
    ?_, ?_, ?_, ?_⟩
  · intro k
    simp only [Q, q, ContinuousMap.sub_apply, ContinuousMap.one_apply, ContinuousMap.smul_apply,
      squareDisplacement_apply, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_mul]
  · intro k
    dsimp only [q]
    exact sub_nonneg.mpr ((mul_le_mul_of_nonneg_left (hd k) (inv_nonneg.mpr hC.le)).trans_eq
      (inv_mul_cancel₀ hC.ne'))
  · intro k
    exact sub_le_self _ (mul_nonneg (inv_nonneg.mpr hC.le) (displacementSquared_nonneg k))
  · intro k
    change 1 - C⁻¹ * displacementSquared k = 1 ↔ k = 1
    rw [sub_eq_self, mul_eq_zero, or_iff_right (inv_ne_zero hC.ne'), displacementSquared_eq_zero]

/-- Positive polynomial weights of unit mass on the orthogonal group can have arbitrarily
small first moment of displacement in the matrix operator norm. -/
def RealPolynomialWeightStatement : Prop :=
  ∀ (r : ℕ) (ε : ℝ), 0 < ε → ∃ (w : C(Matrix.unitaryGroup (Fin (r + 1)) ℝ, ℂ)) (W : Kc (r + 1) → ℝ),
    w ∈ polynomialStar (r + 1) ∧ Continuous W ∧ (∀ k, 0 ≤ W k) ∧
    (∀ k, compactWeight w k = (W k : ℂ)) ∧
    (∫ k, W k ∂haarK (r + 1)) = 1 ∧
    (∫ k, W k * ‖((k.val : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) - 1)‖ ∂haarK (r + 1)) < ε

set_option maxHeartbeats 700000 in
theorem realPolynomialWeight : RealPolynomialWeightStatement := by
  intro r ε hε
  let n := r + 1
  let μ := haarK n
  obtain ⟨q, Q, hQ, hqc, hqQ, hq₀, hq₁, hqeq⟩ := exists_positive_peak n
  have hqOne : q 1 = 1 := (hqeq 1).mpr rfl
  have hpeak (U : Set (Kc n)) (hU : IsOpen U) (h1 : 1 ∈ U) :
      ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ k ∉ U, q k ≤ c := by
    by_cases h : Uᶜ.Nonempty
    · obtain ⟨u, hu, hMax⟩ := hU.isClosed_compl.isCompact.exists_isMaxOn h hqc.continuousOn
      refine ⟨q u, hq₀ u, lt_of_le_of_ne (hq₁ u) (fun hh => hu ((hqeq u).mp hh ▸ h1)), ?_⟩
      exact fun k hk => hMax hk
    · exact ⟨0, le_rfl, zero_lt_one, fun k hk => (h ⟨k, hk⟩).elim⟩
  let d (k : Kc n) := ‖(k.val : Matrix (Fin n) (Fin n) ℝ) - 1‖
  have hd : Continuous d := continuous_displacement n
  let F (k : Kc n) : ℂ := ((1 - ε⁻¹ * d k : ℝ) : ℂ)
  have hF : Continuous F :=
    Complex.continuous_ofReal.comp (continuous_const.sub (continuous_const.mul hd))
  have hF₁ : F 1 = 1 := by simp [F, d]
  have hInt {V : Type} [NormedAddCommGroup V] {f : Kc n → V} (hf : Continuous f) :
      Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨j, hj⟩ := exists_pos_integral_pow_of_peak μ hF (hInt hF) hF₁ hqc hq₀ hq₁ hqOne hpeak
  let Z : ℝ := ∫ k, q k ^ j ∂μ
  have hZ : 0 < Z := (hqc.pow j).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun k => pow_nonneg (hq₀ k) _) (x := (1 : Kc n))
    (by simp [hqOne])
  let W (k : Kc n) := Z⁻¹ * q k ^ j
  let w : C(Matrix.unitaryGroup (Fin n) ℝ, ℂ) := ((Z⁻¹ : ℝ) : ℂ) • Q ^ j
  have hW : Continuous W := continuous_const.mul (hqc.pow _)
  have hw (k : Kc n) : compactWeight w k = (W k : ℂ) := by
    change w (unitaryCompactMatrix ℝ n k) = _
    simp only [w, W, ContinuousMap.smul_apply, ContinuousMap.pow_apply, hqQ, smul_eq_mul,
      Complex.ofReal_mul, Complex.ofReal_pow]
  refine ⟨w, W, (polynomialStar n).toSubalgebra.smul_mem (pow_mem hQ _) _, hW,
    fun k => mul_nonneg (inv_nonneg.mpr hZ.le) (pow_nonneg (hq₀ k) _), hw, ?_, ?_⟩
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
    have he : (fun k => W k * d k) = fun k => Z⁻¹ * (d k * q k ^ j) :=
      funext fun k => by change Z⁻¹ * q k ^ j * d k = _; ring
    change (∫ k, W k * d k ∂μ) < ε
    rw [he, integral_const_mul, ← div_eq_inv_mul]
    exact (div_lt_iff₀ hZ).mpr hm

/-! ## Approximation of right translates -/

/-- A positive unit-mass compact average with small displacement moment approximates the value
at the identity of a continuous function. -/
private theorem average_close {φ : Kc n → ℂ} (hφ : Continuous φ) {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (W : Kc n → ℝ), Continuous W → (∀ k, 0 ≤ W k) →
      (∫ k, W k ∂haarK n) = 1 →
      ‖(∫ k, (W k : ℂ) * φ k ∂haarK n) - φ 1‖ ≤
        η + A * ∫ k, W k * ‖((k.val : Matrix (Fin n) (Fin n) ℝ) - 1)‖ ∂haarK n := by
  let μ := haarK n
  let d (k : Kc n) := ‖(k.val : Matrix (Fin n) (Fin n) ℝ) - 1‖
  have hd : Continuous d := continuous_displacement n
  obtain ⟨M, hM⟩ := (isCompact_range hφ.norm).bddAbove
  let M' := max M 0
  have hφM (k : Kc n) : ‖φ k‖ ≤ M' := (hM (mem_range_self k)).trans (le_max_left _ _)
  -- continuity at the identity
  have hU : IsOpen {k : Kc n | ‖φ k - φ 1‖ < η} :=
    isOpen_lt (hφ.sub continuous_const).norm continuous_const
  have h1U : (1 : Kc n) ∈ {k : Kc n | ‖φ k - φ 1‖ < η} := by simpa using hη
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ k : Kc n, d k < δ → ‖φ k - φ 1‖ < η := by
    have hcont : ContinuousAt (fun k : Kc n => ‖φ k - φ 1‖) 1 :=
      ((hφ.sub continuous_const).norm).continuousAt
    have hd1 : d 1 = 0 := by simp [d]
    -- use the metric induced by the displacement
    have hemb : Topology.IsEmbedding ((Units.val : Langlands.GeneralLinear n ℝ →
        Matrix (Fin n) (Fin n) ℝ) ∘ (Subtype.val : Kc n → Langlands.GeneralLinear n ℝ)) :=
      Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    have hnhds := hU.mem_nhds h1U
    rw [hemb.nhds_eq_comap] at hnhds
    obtain ⟨t, ht, hts⟩ := Filter.mem_comap.mp hnhds
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
    refine ⟨δ, hδ, fun k hk => hts (hball ?_)⟩
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [d] using hk
  let A := 2 * M' / δ
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A, hA, fun W hW hW₀ hW₁ => ?_⟩
  have hInt {V : Type} [NormedAddCommGroup V] {f : Kc n → V} (hf : Continuous f) :
      Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpt (k : Kc n) : ‖φ k - φ 1‖ ≤ η + A * d k := by
    by_cases hk : d k < δ
    · exact (hball k hk).le.trans (le_add_of_nonneg_right (mul_nonneg hA (norm_nonneg _)))
    · have hk' : 1 ≤ d k / δ := (one_le_div hδ).mpr (le_of_not_gt hk)
      calc ‖φ k - φ 1‖ ≤ ‖φ k‖ + ‖φ 1‖ := norm_sub_le _ _
        _ ≤ 2 * M' := by linarith [hφM k, hφM 1]
        _ ≤ 2 * M' * (d k / δ) := le_mul_of_one_le_right (by positivity) hk'
        _ = A * d k := by dsimp only [A]; ring
        _ ≤ η + A * d k := le_add_of_nonneg_left hη.le
  have hdiff : (∫ k, (W k : ℂ) * φ k ∂μ) - φ 1 = ∫ k, (W k : ℂ) * (φ k - φ 1) ∂μ := by
    have h1 : (∫ k, (W k : ℂ) * φ 1 ∂μ) = φ 1 := by
      rw [integral_mul_const, integral_complex_ofReal, hW₁, Complex.ofReal_one, one_mul]
    have hsplit : (∫ k, (W k : ℂ) * (φ k - φ 1) ∂μ) =
        (∫ k, (W k : ℂ) * φ k ∂μ) - ∫ k, (W k : ℂ) * φ 1 ∂μ := by
      have hI1 : Integrable (fun k => (W k : ℂ) * φ k) μ :=
        hInt ((Complex.continuous_ofReal.comp hW).mul hφ)
      have hI2 : Integrable (fun k => (W k : ℂ) * φ 1) μ :=
        hInt ((Complex.continuous_ofReal.comp hW).mul continuous_const)
      rw [← integral_sub hI1 hI2]
      exact integral_congr_ae (ae_of_all _ fun k => by ring)
    rw [hsplit, h1]
  rw [hdiff]
  calc ‖∫ k, (W k : ℂ) * (φ k - φ 1) ∂μ‖ ≤ ∫ k, W k * (η + A * d k) ∂μ := by
        refine norm_integral_le_of_norm_le (hInt (hW.mul (continuous_const.add
          (continuous_const.mul hd)))) (ae_of_all _ fun k => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hW₀ k)]
        exact mul_le_mul_of_nonneg_left (hpt k) (hW₀ k)
    _ = η * (∫ k, W k ∂μ) + A * ∫ k, W k * d k ∂μ := by
        have hsum : (∫ k, (η * W k + A * (W k * d k)) ∂μ) =
            (∫ k, η * W k ∂μ) + ∫ k, A * (W k * d k) ∂μ :=
          integral_add (hInt (continuous_const.mul hW)) (hInt (continuous_const.mul (hW.mul hd)))
        rw [integral_const_mul, integral_const_mul] at hsum
        rw [← hsum]
        exact integral_congr_ae (ae_of_all _ fun k => by ring)
    _ = η + A * ∫ k, W k * d k ∂μ := by rw [hW₁, mul_one]

/-- A right translate of a value of a specified real Whittaker intertwiner is the pointwise
limit of values of the same intertwiner, each obtained by a positive unit-mass compact average
of that translate with a polynomial weight. -/
def RealWhittakerRightTranslateApproximationStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock) (a : ℝˣ)
    (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)), IsRealWhittakerIntertwiner r ds a B →
  ∀ (f : Std (r + 1) ds) (g : G (r + 1)),
    ∃ (p : ℕ → Std (r + 1) ds) (w : ℕ → Kc (r + 1) → ℝ),
      (∀ j, Continuous (w j)) ∧ (∀ j k, 0 ≤ w j k) ∧
      (∀ j, (∫ k, w j k ∂haarK (r + 1)) = 1) ∧
      (∀ j x, B (p j) x = ∫ k, (w j k : ℂ) * B f (x * k.val * g) ∂haarK (r + 1)) ∧
      ∀ x, Tendsto (fun j => B (p j) x) atTop (𝓝 (B f (x * g)))

set_option maxHeartbeats 900000 in
theorem realWhittakerRightTranslateApproximation :
    RealWhittakerRightTranslateApproximationStatement := by
  intro r ds a B hB f g
  let n := r + 1
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  choose w W hpoly hWc hW₀ hwW hW₁ hMoment using fun j : ℕ => realPolynomialWeight r (ε j) (hε j)
  choose p hp hBp using fun j : ℕ => realExactCompactProjection r ds a (haarK n) inferInstance
    (compactWeight (w j)) (finiteDimensional_compactWeight (hpoly j)) B hB f g
  refine ⟨p, W, hWc, hW₀, hW₁, fun j x => ?_, fun x => ?_⟩
  · rw [hBp j x]
    exact integral_congr_ae (ae_of_all _ fun k => by simp only [hwW j k])
  · let φ : Kc n → ℂ := fun k => B f (x * k.val * g)
    have hφ : Continuous φ := (hB.2.1 f).continuous.comp
      ((continuous_const.mul continuous_subtype_val).mul continuous_const)
    have hφ1 : φ 1 = B f (x * g) := by simp [φ]
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨A, hA, hclose⟩ := average_close hφ (half_pos hη)
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * A / η)
    refine ⟨N, fun j hj => ?_⟩
    have hval : B (p j) x = ∫ k, (W j k : ℂ) * φ k ∂haarK n := by
      rw [hBp j x]
      exact integral_congr_ae (ae_of_all _ fun k => by simp only [hwW j k, φ])
    rw [dist_eq_norm, hval, ← hφ1]
    have hbound := hclose (W j) (hWc j) (hW₀ j) (hW₁ j)
    have hεj : A * ε j < η / 2 := by
      have hj' : (2 * A / η) < (j : ℝ) + 1 := by
        have : (N : ℝ) ≤ j := by exact_mod_cast hj
        linarith
      have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      dsimp only [ε]
      rw [mul_one_div, div_lt_iff₀ hpos]
      rw [div_lt_iff₀ hη] at hj'
      linarith
    calc _ ≤ η / 2 + A * ∫ k, W j k * ‖((k.val : Matrix (Fin n) (Fin n) ℝ) - 1)‖ ∂haarK n :=
          hbound
      _ ≤ η / 2 + A * ε j := by
          gcongr
          exact (hMoment j).le
      _ < η := by linarith

end Langlands.Global.RankinSelbergGlobal.RealWhittakerRightTranslateApproximation
