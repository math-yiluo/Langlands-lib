import Langlands.Algebra.WordSeriesEvaluation
import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialChart
import Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution

/-! # Small analytic conjugators for products of exponentials -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Metric Set PowerSeries Langlands.CyclicWords Langlands.FormalPowerSeries
open scoped ENNReal NNReal

variable (F : Type*) [NontriviallyNormedField F] [IsUltrametricDist F] [CharZero F]

private theorem exists_factorial_scale : ∃ s : F, 0 < ‖s‖ ∧ ‖s‖ ≤ 1 ∧
    ∀ k : ℕ, 0 < k → ‖((k.factorial : F)⁻¹)‖ * ‖s‖ ^ k ≤ ‖s‖ := by
  have hRad : 0 < (NormedSpace.expSeries F F).radius := exponentialPositiveRadius F F
  obtain ⟨ρ, hρ₀, hρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hRad
  have hρpos : 0 < (ρ : ℝ) := by exact_mod_cast hρ₀
  obtain ⟨C, hC, hb⟩ := (NormedSpace.expSeries F F).norm_mul_pow_le_of_lt_radius hρ
  have hFac (k : ℕ) : ‖((k.factorial : F)⁻¹)‖ * (ρ : ℝ) ^ k ≤ C := by
    have h : ‖((k.factorial : F)⁻¹)‖ ≤ ‖NormedSpace.expSeries F F k‖ := by
      have h := (NormedSpace.expSeries F F k).le_opNorm (fun _ => (1 : F))
      simpa only [NormedSpace.expSeries_apply_eq, one_pow, smul_eq_mul, mul_one, norm_one,
        Finset.prod_const_one] using h
    exact (mul_le_mul_of_nonneg_right h (by positivity)).trans (hb k)
  obtain ⟨s, hs, hsr⟩ := NormedField.exists_norm_lt F
    (show 0 < min (1 : ℝ) (min (ρ : ℝ) ((ρ : ℝ) ^ 2 / C)) from
      lt_min zero_lt_one (lt_min hρpos (div_pos (pow_pos hρpos _) hC)))
  have hs₁ : ‖s‖ ≤ 1 := hsr.le.trans (min_le_left _ _)
  have hsρ : ‖s‖ ≤ (ρ : ℝ) := hsr.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsC : ‖s‖ ≤ (ρ : ℝ) ^ 2 / C := hsr.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨s, hs, hs₁, fun k hk => ?_⟩
  by_cases hOne : k = 1
  · subst k; simp
  have hk₂ : 2 ≤ k := by omega
  let a := ‖s‖ / (ρ : ℝ)
  have ha : 0 ≤ a := div_nonneg hs.le hρpos.le
  have ha₁ : a ≤ 1 := (div_le_one₀ hρpos).mpr hsρ
  calc
    _ = (‖((k.factorial : F)⁻¹)‖ * (ρ : ℝ) ^ k) * a ^ k := by
      rw [mul_assoc, ← mul_pow, show (ρ : ℝ) * a = ‖s‖ by dsimp [a]; field_simp]
    _ ≤ C * a ^ k := mul_le_mul_of_nonneg_right (hFac k) (pow_nonneg ha _)
    _ ≤ C * a ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ha ha₁ hk₂) hC.le
    _ ≤ ‖s‖ := by
      have h := (le_div_iff₀ hC).mp hsC
      dsimp [a]
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ (pow_pos hρpos _)]
      nlinarith [mul_le_mul_of_nonneg_left h hs.le]

variable (A : Type*) [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A] [CompleteSpace A]

/-- A pair of families of small conjugators with uniform Lipschitz bounds for the units
and their inverses, for evaluating the exponential product identity. -/
def SmallExponentialConjugatorsStatement (F A : Type*) [NontriviallyNormedField F]
    [IsUltrametricDist F] [CharZero F] [NormedRing A] [NormedAlgebra F A]
    [IsUltrametricDist A] [CompleteSpace A] : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∃ ε > (0 : ℝ),
    let B := closedBall (0 : A × A) ε
    ∃ U : Bool → B → Aˣ,
      (∀ b x, ‖(U b x : A) - 1‖ ≤ c * ‖(x : A × A)‖ ∧ ‖(↑(U b x)⁻¹ : A)‖ ≤ max 1 ‖(1 : A)‖) ∧
      (∀ b x y, ‖(U b x : A) - (U b y : A)‖ ≤ c * ‖(x : A × A) - (y : A × A)‖ ∧
        ‖(↑(U b x)⁻¹ : A) - (↑(U b y)⁻¹ : A)‖ ≤ c * ‖(x : A × A) - (y : A × A)‖) ∧
      (∀ x, NormedSpace.exp (conjugationHomeomorph (U false x) x.val.1 +
        conjugationHomeomorph (U true x) x.val.2) = NormedSpace.exp x.val.1 * NormedSpace.exp x.val.2)

set_option maxHeartbeats 4300000 in
theorem smallExponentialConjugators : SmallExponentialConjugatorsStatement F A := by
  obtain ⟨s, hs, hs₁, hFac⟩ := exists_factorial_scale F
  have hs₀ : s ≠ 0 := norm_pos_iff.mp hs
  obtain ⟨u, v, hu₀, hv₀, hu, hv, hExp⟩ := formalExponentialStraightening s hs₀ hs₁ hFac
  let S := PowerSeries (WordPolynomial F)
  let k (b : Bool) : Sˣ := if b then v else u
  have hk₀ (b : Bool) : constantCoeff (k b : S) = 1 := by cases b <;> simpa [k] using ‹_›
  have hk (b : Bool) : WordSeriesControl 1 (k b : S) := by cases b <;> simpa [k] using ‹_›
  have hkInv (b : Bool) : WordSeriesControl 1 ((↑(k b)⁻¹ : S)) := WordSeriesControl.inv_unit _ (hk₀ b) (hk b)
  let K := max (1 : ℝ) ‖(1 : A)‖
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  let R := 1 / (2 * K)
  have hR₀ : 0 < R := by dsimp [R]; positivity
  have hKR : K * R < 1 := by dsimp [R]; field_simp; linarith
  have hR : R < 1 := (le_mul_of_one_le_left hR₀.le hK).trans_lt hKR
  let ε := ‖s‖ * R
  let B := closedBall (0 : A × A) ε
  let q (x : B) : A × A := s⁻¹ • x.val
  have hNorm (x : B) : ‖q x‖ = ‖s‖⁻¹ * ‖x.val‖ := by
    change ‖s⁻¹ • x.val‖ = _
    rw [norm_smul, norm_inv]
  have hSmall (x : B) : ‖q x‖ ≤ R := by
    have hx : ‖x.val‖ ≤ ε := dist_zero_right x.val ▸ x.property
    rw [hNorm]
    exact (mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hs.le)).trans_eq (by dsimp [ε]; field_simp)
  have hDiff (x y : B) : ‖q x - q y‖ = ‖s‖⁻¹ * ‖x.val - y.val‖ := by
    change ‖s⁻¹ • x.val - s⁻¹ • y.val‖ = _
    rw [← smul_sub, norm_smul, norm_inv]
  let U (b : Bool) (x : B) : Aˣ := seriesEvalUnit (hSmall x) hR (k b) (hk₀ b) (hk b)
  let c := max 1 ((K / R) * ‖s‖⁻¹)
  have hc : (K / R) * ‖s‖⁻¹ ≤ c := le_max_right _ _
  have hc' : K * ‖s‖⁻¹ ≤ c :=
    (mul_le_mul_of_nonneg_right ((le_div_iff₀ hR₀).mpr (mul_le_of_le_one_right hKpos.le hR.le))
      (inv_nonneg.mpr hs.le)).trans hc
  refine ⟨c, le_max_left _ _, ε, mul_pos hs hR₀, U, ?_, ?_, ?_⟩
  · intro b x
    have hx := hSmall x
    have hr := hx.trans_lt hR
    have hZero : VanishesBelow 1 ((k b : S) - 1) := fun n hn => by
      have h : n = 0 := by omega
      rw [h, map_sub, show coeff 0 (1 : S) = 1 by simp [PowerSeries.coeff_one],
        coeff_zero_eq_constantCoeff_apply, hk₀, sub_self]
    have hBound := norm_seriesEval_le_of_vanishesBelow (x := q x) (r := ‖q x‖) le_rfl hr
      ((hk b).sub (WordSeriesControl.one (F := F))) hZero
    have hClose : ‖(U b x : A) - 1‖ ≤ K * ‖q x‖ := by
      change ‖seriesEval (F := F) (q x) (k b : S) - 1‖ ≤ _
      have hSub := seriesEval_sub (x := q x) hx hR (hk b) (WordSeriesControl.one (F := F))
      rw [seriesEval_one] at hSub
      simpa only [hSub, mul_one, pow_one] using hBound
    refine ⟨hClose.trans ?_, ?_⟩
    · rw [hNorm, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hc' (norm_nonneg _)
    · change ‖seriesEval (F := F) (q x) (↑(k b)⁻¹ : S)‖ ≤ K
      simpa only [mul_one, pow_zero] using
        norm_seriesEval_le_of_vanishesBelow hx hR (hkInv b) (vanishesBelow_zero _)
  · intro b x y
    constructor
    · change ‖seriesEval (F := F) (q x) (k b : S) - seriesEval (F := F) (q y) (k b : S)‖ ≤ _
      apply (norm_seriesEval_sub_le (hSmall x) (hSmall y) hR₀ hR (hk b)).trans
      rw [hDiff, mul_one, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    · change ‖seriesEval (F := F) (q x) (↑(k b)⁻¹ : S) - seriesEval (F := F) (q y) (↑(k b)⁻¹ : S)‖ ≤ _
      apply (norm_seriesEval_sub_le (hSmall x) (hSmall y) hR₀ hR (hkInv b)).trans
      rw [hDiff, mul_one, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  · intro x
    let p := q x
    have hp : ‖p‖ ≤ R := hSmall x
    let C (b : Bool) := (k b : S) * seriesLetter b * (↑(k b)⁻¹ : S)
    have hC (b : Bool) : WordSeriesControl 1 (C b) := by
      simpa only [C, mul_one] using ((hk b).mul (seriesLetter_control b)).mul (hkInv b)
    let e := s • (C false + C true)
    let l (b : Bool) := s • seriesLetter (F := F) b
    have he : WordSeriesControl ‖s‖ e := by simpa only [e, mul_one] using ((hC false).add (hC true)).smul s
    have hl (b : Bool) : WordSeriesControl ‖s‖ (l b) := by simpa only [l, mul_one] using (seriesLetter_control b).smul s
    have hLetter (b : Bool) : constantCoeff (seriesLetter (F := F) b) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, seriesLetter, coeff_monomial, ite_eq_right (by decide)]
    have hC₀ (b : Bool) : constantCoeff (C b) = 0 := by
      change constantCoeff ((k b : S) * seriesLetter b * (↑(k b)⁻¹ : S)) = 0
      rw [map_mul, map_mul, hLetter, mul_zero, zero_mul]
    have he₀ : VanishesBelow 1 e := fun n hn => by
      have hn₀ : n = 0 := by omega
      rw [hn₀, coeff_zero_eq_constantCoeff_apply]
      change constantCoeff (s • (C false + C true) : PowerSeries (WordPolynomial F)) = 0
      rw [constantCoeff_smul, map_add, hC₀, hC₀, add_zero, smul_zero]
    have hl₀ (b : Bool) : VanishesBelow 1 (l b) := fun n hn => by
      have hn₀ : n = 0 := by omega
      rw [hn₀, coeff_zero_eq_constantCoeff_apply]
      change constantCoeff (s • seriesLetter (F := F) b) = 0
      rw [constantCoeff_smul, hLetter, smul_zero]
    have hEx := congrArg (seriesEval (F := F) p) hExp
    change seriesEval (F := F) p (formalExponential F e) =
      seriesEval (F := F) p (formalExponential F (l false) * formalExponential F (l true)) at hEx
    have hExpBound (b : Bool) : WordSeriesControl 1 (formalExponential F (l b)) := by
      have h := ((WordSeriesControl.exponentialControl _ _ (hl b) hFac).mono hs₁).add (WordSeriesControl.one (F := F))
      simpa only [sub_add_cancel] using h
    rw [seriesEval_mul hp hR (hExpBound false) (hExpBound true),
      wordSeriesExponentialEvaluation (F := F) (A := A) p R _ hp hR hKR hs₁ e he he₀ hFac,
      wordSeriesExponentialEvaluation (F := F) (A := A) p R _ hp hR hKR hs₁ (l false) (hl false) (hl₀ false) hFac,
      wordSeriesExponentialEvaluation (F := F) (A := A) p R _ hp hR hKR hs₁ (l true) (hl true) (hl₀ true) hFac] at hEx
    have hlVal (b : Bool) : seriesEval (F := F) p (l b) = if b then x.val.2 else x.val.1 := by
      change seriesEval (F := F) p (s • seriesLetter b) = _
      rw [seriesEval_smul hp hR (seriesLetter_control b), seriesEval_letter]
      cases b <;> simp [p, q, smul_smul, mul_inv_cancel₀ hs₀]
    have hCVal (b : Bool) : s • seriesEval (F := F) p (C b) =
        conjugationHomeomorph (U b x) (if b then x.val.2 else x.val.1) := by
      change s • seriesEval (F := F) p ((k b : S) * seriesLetter b * (↑(k b)⁻¹ : S)) = _
      rw [seriesEval_mul hp hR ((hk b).mul (seriesLetter_control b)) (hkInv b),
        seriesEval_mul hp hR (hk b) (seriesLetter_control b), ← smul_mul_assoc, ← mul_smul_comm,
        ← seriesEval_smul hp hR (seriesLetter_control b)]
      change _ * seriesEval (F := F) p (l b) * _ = _
      rw [hlVal]
      rfl
    change NormedSpace.exp (seriesEval (F := F) p (s • (C false + C true))) = _ at hEx
    rw [seriesEval_smul hp hR ((hC false).add (hC true)), seriesEval_add hp hR (hC false) (hC true),
      smul_add, hCVal false, hCVal true, hlVal false, hlVal true] at hEx
    exact hEx

end Langlands.HarmonicAnalysis.UnitConjugation
