import Langlands.Global.RankinSelberg.ComplexWhittakerTranslateExtension

/-! # Simultaneous compact-finite approximation under genuine right translation -/

noncomputable section

open MeasureTheory Set
open scoped Classical ContDiff Matrix.Norms.Operator Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexSmoothTranslateDensity

open Langlands.Archimedean (continuous_unitary_toUnits matrixModel)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCentralPolynomialWeight (complexCentralPolynomialWeight)
open ComplexCompactDifferenceDensity (convolution convolution_error exists_standard_convolution)
open ComplexCompactDifferences (displacementProduct displacementProduct_nonneg)
open ComplexCompactSmoothDifferences (compactConvexHull compactFunctionDifference CompactMatrixJetBound
  CompactProfileDifferenceBound complexCompactSmoothDifferences matrixDifference_jet_bound_on)
open ComplexGodement (compactMatrixHaar)
open ComplexWhittakerSmoothExtension (SmoothStandard compactProfile finiteToSmooth
  exists_smooth_matrix_extension exists_smooth_compact_difference_bound)
open ComplexWhittakerTranslateExtension (smoothTranslate)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Std" => Automorphic.complexStandardKFinite

local instance smoothTranslateDensityMeasurable (n : ℕ) : MeasurableSpace (K n) := borel _
local instance smoothTranslateDensityBorel (n : ℕ) : BorelSpace (K n) := ⟨rfl⟩

variable {n : ℕ} {ds : List ComplexCharacterData}
local notation "νK" => compactMatrixHaar n

private theorem exists_compactHull_norm_bound (n : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ x ∈ compactConvexHull n, ‖x‖ ≤ M := by
  obtain ⟨A, hA⟩ := (isCompact_range (continuous_subtype_val.norm :
    Continuous (fun k : K n => ‖k.val‖))).bddAbove
  let M := max 1 A
  have hHull : compactConvexHull n ⊆ Metric.closedBall 0 M :=
    convexHull_min (fun x hx => mem_closedBall_zero_iff.mpr
      ((hA (mem_range_self (⟨x, hx⟩ : K n))).trans (le_max_right _ _)))
      (convex_closedBall _ _)
  exact ⟨M, le_max_left _ _, fun x hx => mem_closedBall_zero_iff.mp (hHull hx)⟩

/-- For a fixed group element, a further right compact move changes the translated compact
profile by at most a uniform multiple of the move's displacement in every fixed difference order. -/
theorem exists_translate_difference_bound (g : G n) {F : G n → ℂ}
    (hF : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ F) (J : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ k : K n, CompactProfileDifferenceBound J
      (fun x => F (Unitary.toUnits x * g * Unitary.toUnits k) - F (Unitary.toUnits x * g))
      (D * ‖k.val - 1‖) := by
  let T : K n × K n → G n := fun p => Unitary.toUnits p.1 * g * Unitary.toUnits p.2
  let S := range (fun p => (T p).val)
  have hc : Continuous T := ((continuous_unitary_toUnits.comp continuous_fst).mul continuous_const).mul
    (continuous_unitary_toUnits.comp continuous_snd)
  have hS : IsCompact S := isCompact_range (Units.continuous_val.comp hc)
  obtain ⟨H, hH, hCompact, hAgree⟩ := exists_smooth_matrix_extension hS
    (fun _ ⟨p, hp⟩ => hp ▸ (T p).isUnit) hF
  obtain ⟨D, hD, hDeriv⟩ := hCompact.exists_bound_iteratedFDeriv hH (J + 1)
  obtain ⟨M₀, hM₀, hHull⟩ := exists_compactHull_norm_bound n
  obtain ⟨C, hC, hProfile⟩ := complexCompactSmoothDifferences n J
  let P := max 1 ‖g.val‖
  let M := M₀ * P
  have hP : 1 ≤ P := le_max_left _ _
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hM₀ hP
  have hM₀M : M₀ ≤ M := le_mul_of_one_le_right (zero_le_one.trans hM₀) hP
  let A : Mat n →L[ℝ] Mat n := (ContinuousLinearMap.mul ℝ (Mat n)).flip g.val
  have hA : ‖A‖ ≤ P := ContinuousLinearMap.opNorm_le_bound A (zero_le_one.trans hP) fun x =>
    (norm_mul_le x g.val).trans ((mul_le_mul_of_nonneg_left (le_max_right 1 ‖g.val‖) (norm_nonneg x)).trans_eq
      (mul_comm _ _))
  let E := M ^ J * (M + J) * D * P ^ J
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨C * E, mul_nonneg (zero_le_one.trans hC) hE, fun k => ?_⟩
  let Fk (x : Mat n) := H (x * k.val) - H x
  have hFk : ContDiff ℝ ∞ Fk := (hH.comp ((ContinuousLinearMap.mul ℝ (Mat n)).flip k.val).contDiff).sub hH
  have hk : ‖k.val‖ ≤ M := (hHull k.val (subset_convexHull ℝ _ k.2)).trans hM₀M
  have hJets : CompactMatrixJetBound J (Fk ∘ A) (E * ‖k.val - 1‖) := by
    intro i hi x hx
    have hAx : ‖A x‖ ≤ M := (norm_mul_le x g.val).trans
      (mul_le_mul (hHull x hx) (le_max_right 1 ‖g.val‖) (norm_nonneg _) (zero_le_one.trans hM₀))
    have hOne : ‖iteratedFDeriv ℝ i Fk (A x)‖ ≤ M ^ i * (M + i) * D * ‖k.val - 1‖ :=
      matrixDifference_jet_bound_on (S := univ) (convex_univ : Convex ℝ (univ : Set (Mat n)))
        hH hM hD (fun j hj y _ => hDeriv j (hj.trans (Nat.succ_le_succ hi)) y) k hk
        (mem_univ _) (mem_univ _) hAx
    have hiFinite : (i : WithTop ℕ∞) ≤ ∞ := (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top i)).le
    rw [A.iteratedFDeriv_comp_right hFk x hiFinite]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      _ ≤ (M ^ J * (M + J) * D * ‖k.val - 1‖) * P ^ J := by
        have hCoef : M ^ i * (M + i) ≤ M ^ J * (M + J) :=
          mul_le_mul (pow_le_pow_right₀ hM hi) (add_le_add le_rfl (Nat.cast_le.mpr hi))
            (by positivity) (by positivity)
        exact mul_le_mul
          (hOne.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCoef hD) (norm_nonneg _)))
          ((pow_le_pow_left₀ (norm_nonneg A) hA i).trans (pow_le_pow_right₀ hP hi))
          (by positivity) (by positivity)
      _ = _ := by dsimp only [E]; ring
  have hValues : (fun x : K n => F (Unitary.toUnits x * g * Unitary.toUnits k) - F (Unitary.toUnits x * g)) =
      fun x => (Fk ∘ A) x.val := by
    funext x
    have hx₁ : (Unitary.toUnits x * g * Unitary.toUnits k).val ∈ S := mem_range_self (x, k)
    have hx₀ : (Unitary.toUnits x * g).val ∈ S := ⟨(x, 1), by simp [T]⟩
    change F (Unitary.toUnits x * g * Unitary.toUnits k) - F (Unitary.toUnits x * g) =
      H (Unitary.toUnits x * g * Unitary.toUnits k).val - H (Unitary.toUnits x * g).val
    rw [hAgree _ hx₁, hAgree _ hx₀]
  rw [hValues, mul_assoc C E]
  exact hProfile _ _ (hFk.comp A.contDiff) (mul_nonneg hE (norm_nonneg _)) hJets

private theorem integrable_compact {E : Type*} [NormedAddCommGroup E] {F : K n → E}
    (hF : Continuous F) : Integrable F νK :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem continuous_difference_parameter (H : K n → K n → ℂ) (hH : ∀ x, Continuous (fun k => H k x))
    (ks : List (K n)) (x : K n) : Continuous fun k => compactFunctionDifference ks (H k) x := by
  induction ks generalizing x with
  | nil => exact hH x
  | cons y ys ih => exact (ih (x * y)).sub (ih x)

private theorem difference_integral (w : C(K n, ℂ)) (H : K n → K n → ℂ)
    (hH : ∀ x, Continuous (fun k => H k x)) (ks : List (K n)) (x : K n) :
    compactFunctionDifference ks (fun y => ∫ k, w k * H k y ∂νK) x =
      ∫ k, w k * compactFunctionDifference ks (H k) x ∂νK := by
  induction ks generalizing x with
  | nil => rfl
  | cons y ys ih =>
    have hi (z : K n) : Integrable (fun k => w k * compactFunctionDifference ys (H k) z) νK :=
      integrable_compact (w.continuous.mul (continuous_difference_parameter H hH ys z))
    change compactFunctionDifference ys (fun z => ∫ k, w k * H k z ∂νK) (x * y) -
      compactFunctionDifference ys (fun z => ∫ k, w k * H k z ∂νK) x =
      ∫ k, w k * (compactFunctionDifference ys (H k) (x * y) - compactFunctionDifference ys (H k) x) ∂νK
    rw [ih, ih, ← integral_sub (hi (x * y)) (hi x)]
    simp only [mul_sub]

private theorem integrated_difference_bound (w : C(K n, ℂ)) (W : K n → ℝ)
    (hW : Continuous W) (hW₀ : ∀ k, 0 ≤ W k) (hw : ∀ k, w k = (W k : ℂ))
    (H : K n → K n → ℂ) (hH : ∀ x, Continuous (fun k => H k x)) {J : ℕ} {D ε : ℝ} (hD : 0 ≤ D)
    (hBound : ∀ k, CompactProfileDifferenceBound J (H k) (D * ‖k.val - 1‖))
    (hMoment : (∫ k, W k * ‖k.val - 1‖ ∂νK) ≤ ε) :
    CompactProfileDifferenceBound J (fun x => ∫ k, w k * H k x ∂νK) (D * ε) := by
  intro ks hks x
  rw [difference_integral w H hH]
  let R := D * displacementProduct ks
  have hR : 0 ≤ R := mul_nonneg hD (displacementProduct_nonneg ks)
  have hi : Integrable (fun k : K n => R * (W k * ‖k.val - 1‖)) νK :=
    integrable_compact (continuous_const.mul (hW.mul (continuous_subtype_val.sub continuous_const).norm))
  have hN := norm_integral_le_of_norm_le (f := fun k => w k * compactFunctionDifference ks (H k) x) hi
    (ae_of_all _ fun k => ?_)
  · rw [integral_const_mul] at hN
    exact hN.trans ((mul_le_mul_of_nonneg_left hMoment hR).trans_eq (by dsimp only [R]; ring))
  · rw [norm_mul, hw, Complex.norm_real, Real.norm_of_nonneg (hW₀ k)]
    exact (mul_le_mul_of_nonneg_left (hBound k ks hks x) (hW₀ k)).trans_eq (by dsimp only [R]; ring)

/-- Every smooth standard section admits compact-finite approximation that is simultaneous
in the same difference order before and after any one fixed genuine right translation. -/
def ComplexSmoothTranslateDensityStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (F : SmoothStandard n ds) (g : G n) (J : ℕ),
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ε : ℝ, 0 < ε → ∃ f : Std n ds,
      CompactProfileDifferenceBound J (compactProfile (finiteToSmooth f) - compactProfile F) (D * ε) ∧
      CompactProfileDifferenceBound J
        (compactProfile (smoothTranslate g (finiteToSmooth f)) - compactProfile (smoothTranslate g F)) (D * ε)

set_option maxHeartbeats 900000 in
theorem complexSmoothTranslateDensity : ComplexSmoothTranslateDensityStatement := by
  intro n ds F g J
  obtain ⟨D, hD, hBase⟩ := exists_smooth_compact_difference_bound F.2.1 (J + 1)
  obtain ⟨E, hE, hTrans⟩ := exists_translate_difference_bound g F.2.1 J
  let φ := compactProfile F
  have hφ : Continuous φ := F.2.1.continuous.comp continuous_unitary_toUnits
  refine ⟨D + E, add_nonneg hD hE, fun ε hε => ?_⟩
  obtain ⟨w, W, hw, hW, hPos, hwW, hCentral, hMass, hMoment⟩ := complexCentralPolynomialWeight n ε hε
  obtain ⟨f, hf⟩ := exists_standard_convolution ds F.val F.2 w hw
  refine ⟨f, ?_, ?_⟩
  · have hφf : compactProfile (finiteToSmooth f) = convolution w φ := by
      funext x
      change f.val (Unitary.toUnits x) = ∫ k : K n, w k * F.val (Unitary.toUnits (x * k)) ∂compactMatrixHaar n
      rw [hf (Unitary.toUnits x)]
      simp_rw [Unitary.toUnits.map_mul]
    rw [hφf]
    have hb := convolution_error w W hW hPos hwW hCentral hMass hφ hD hBase hMoment.le
    exact fun ks hks x => (hb ks hks x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hE) hε.le) (displacementProduct_nonneg ks))
  · let H (k x : K n) := F.val (Unitary.toUnits x * g * Unitary.toUnits k) - F.val (Unitary.toUnits x * g)
    have hH (x : K n) : Continuous (fun k => H k x) :=
      (F.2.1.continuous.comp (continuous_const.mul continuous_unitary_toUnits)).sub continuous_const
    have hφg : compactProfile (smoothTranslate g (finiteToSmooth f)) - compactProfile (smoothTranslate g F) =
        fun x : K n => ∫ k, w k * H k x ∂compactMatrixHaar n := by
      funext x
      let ν := compactMatrixHaar n
      let y := Unitary.toUnits x * g
      change f.val y - F.val y = ∫ k, w k * (F.val (y * Unitary.toUnits k) - F.val y) ∂ν
      have hwMass : ∫ k, w k ∂ν = 1 := by
        simp_rw [hwW]
        rw [integral_complex_ofReal, hMass, Complex.ofReal_one]
      have hConst : ∫ k, w k * F.val y ∂ν = F.val y := by rw [integral_mul_const, hwMass, one_mul]
      have hLeft : Integrable (fun k : K n => w k * F.val (y * Unitary.toUnits k)) ν :=
        integrable_compact (w.continuous.mul (F.2.1.continuous.comp (continuous_const.mul continuous_unitary_toUnits)))
      have hRight : Integrable (fun k : K n => w k * F.val y) ν :=
        integrable_compact (w.continuous.mul continuous_const)
      simp_rw [mul_sub]
      rw [integral_sub hLeft hRight, hConst, hf y]
    rw [hφg]
    have hb := integrated_difference_bound w W hW hPos hwW H hH hE hTrans hMoment.le
    exact fun ks hks x => (hb ks hks x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hD) hε.le) (displacementProduct_nonneg ks))

end Langlands.Global.RankinSelbergGlobal.ComplexSmoothTranslateDensity
