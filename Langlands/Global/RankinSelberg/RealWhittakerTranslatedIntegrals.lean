import Langlands.Global.RankinSelberg.RealWhittakerRightTranslateApproximation
import Langlands.Global.RankinSelberg.RealUnequalMellinReduction
import Langlands.Global.RankinSelberg.RealUnequalDualFamily
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Weighted unequal-rank identities on real Whittaker right translates -/

noncomputable section

open MeasureTheory Filter
open scoped Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealWhittakerTranslatedIntegrals

open Langlands.LocalFactor.Archimedean (RealBlock)
open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.RealPrincipalSeriesDuality (haarK)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal
open RealUnequalFamily (HasLeftCharacter continuous_integrand continuous_dualKernel)
open RealUnequalMellinReduction (quotientDetAbs continuous_quotientDetAbs)
open RealWhittakerRightTranslateApproximation (realWhittakerRightTranslateApproximation)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel
  archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "Std" => Automorphic.realStandardKFinite
local notation "R" => fun r t => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ
local notation "ρ" => ArchimedeanLocal.translateFunction
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

local instance translatedIntegralsUnitaryMeasurable (n : ℕ) : MeasurableSpace (unitaryCompact ℝ n) :=
  borel _
local instance translatedIntegralsUnitaryBorel (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

private theorem norm_compactAverage_le {n : ℕ} (w : KU n → ℝ) (fw : Continuous w)
    (hPos : ∀ k, 0 ≤ w k) (hMass : (∫ k, w k ∂haarK n) = 1)
    (f : KU n → ℂ) (M : ℝ) (h : ∀ k, ‖f k‖ ≤ M) :
    ‖∫ k, (w k : ℂ) * f k ∂haarK n‖ ≤ M := by
  have hI : Integrable w (haarK n) :=
    fw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace w)
  calc
    _ ≤ ∫ k, w k * M ∂haarK n := by
      apply norm_integral_le_of_norm_le (hI.mul_const M)
      exact ae_of_all _ fun k => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hPos k)]
        exact mul_le_mul_of_nonneg_left (h k) (hPos k)
    _ = M := by rw [integral_mul_const, hMass, one_mul]

private theorem norm_compactAverage_pair_le {n m : ℕ} (w : KU n → ℝ) (v : KU m → ℝ)
    (hw : Continuous w) (hv : Continuous v) (hw₀ : ∀ k, 0 ≤ w k) (hv₀ : ∀ k, 0 ≤ v k)
    (hw₁ : (∫ k, w k ∂haarK n) = 1) (hv₁ : (∫ k, v k ∂haarK m) = 1)
    (F : KU n → ℂ) (H : KU m → ℂ) (c : ℂ) (M : ℝ)
    (h : ∀ k l, ‖F k * H l * c‖ ≤ M) :
    ‖(∫ k, (w k : ℂ) * F k ∂haarK n) *
      (∫ l, (v l : ℂ) * H l ∂haarK m) * c‖ ≤ M := by
  let y := ∫ l, (v l : ℂ) * H l ∂haarK m
  have hy (k : KU n) : ‖F k * y * c‖ ≤ M := by
    have he : F k * y * c = ∫ l, (v l : ℂ) * (F k * H l * c) ∂haarK m := by
      dsimp only [y]
      rw [← integral_const_mul, ← integral_mul_const]
      apply integral_congr_ae
      exact ae_of_all _ fun l => by dsimp only; ring
    rw [he]
    exact norm_compactAverage_le v hv hv₀ hv₁ (fun l => F k * H l * c) M (h k)
  change ‖(∫ k, (w k : ℂ) * F k ∂haarK n) * y * c‖ ≤ M
  rw [← integral_mul_const, ← integral_mul_const]
  simpa only [mul_assoc] using norm_compactAverage_le w hw hw₀ hw₁ (fun k => F k * y * c) M hy

/-- Ordinary and dual weighted integrands use the same quotient determinant weight. -/
def weightedOrdinary {r t : ℕ} (h : t < r) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (f : ℝ → ℂ) (q : Q t) : ℂ := realUnequalIntegrand h W V 0 q * f (quotientDetAbs q)

def weightedDual {r t : ℕ} (h : t < r) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (f : ℝ → ℂ) (p : Q t × R r t) : ℂ := realUnequalDualKernel h W V 0 p * f (quotientDetAbs p.1)

/-- A weighted integral identity on the values of two specified real Whittaker intertwiners
extends to fixed right translates of their values when each compact family of the two
translated kernels has a common integrable bound. -/
def RealWhittakerTranslatedIntegralsStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es : List RealBlock) (a : ℝˣ) (D : RealQuotientMeasureData t)
    (f f' : ℝ → ℂ), Measurable f → Measurable f' →
    ∀ (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)) (B' : Std (t + 1) es →ₗ[ℂ] (G (t + 1) → ℂ)),
      IsRealWhittakerIntertwiner r ds a B → IsRealWhittakerIntertwiner t es (-a) B' →
    (∀ (p : Std (r + 1) ds) (p' : Std (t + 1) es),
      (∫ q, weightedOrdinary h (B p) (B' p') f q ∂D.measure) =
        ∫ x, weightedDual h (B p) (B' p') f' x ∂realUnequalDualMeasure (r := r) a D) →
    ∀ (v : Std (r + 1) ds) (v' : Std (t + 1) es) (g : G (r + 1)) (g' : G (t + 1))
      (M : Q t → ℝ) (M' : Q t × R r t → ℝ),
      Integrable M D.measure → Integrable M' (realUnequalDualMeasure (r := r) a D) →
      (∀ q (k : KU (r + 1)) (l : KU (t + 1)),
        ‖weightedOrdinary h (ρ (k.val * g) (B v)) (ρ (l.val * g') (B' v')) f q‖ ≤ M q) →
      (∀ p (k : KU (r + 1)) (l : KU (t + 1)),
        ‖weightedDual h (ρ (k.val * g) (B v)) (ρ (l.val * g') (B' v')) f' p‖ ≤ M' p) →
      (∫ q, weightedOrdinary h (ρ g (B v)) (ρ g' (B' v')) f q ∂D.measure) =
        ∫ p, weightedDual h (ρ g (B v)) (ρ g' (B' v')) f' p ∂realUnequalDualMeasure (r := r) a D

set_option maxHeartbeats 1300000 in
theorem realWhittakerTranslatedIntegrals : RealWhittakerTranslatedIntegralsStatement := by
  intro r t h ds es a D f f' hf hf' B B' hB hB' hId v v' g g' M M' hM hM' hBound hBound'
  obtain ⟨U, w, hw, hw₀, hw₁, hU, hUlim⟩ := realWhittakerRightTranslateApproximation r ds a B hB v g
  obtain ⟨V, z, hz, hz₀, hz₁, hV, hVlim⟩ := realWhittakerRightTranslateApproximation t es (-a) B' hB' v' g'
  let μ := D.measure
  let ν := realUnequalDualMeasure (r := r) a D
  let F j := weightedOrdinary h (B (U j)) (B' (V j)) f
  let H j := weightedDual h (B (U j)) (B' (V j)) f'
  have hMeas (j : ℕ) : AEStronglyMeasurable (F j) μ := by
    have hK := continuous_integrand h (hB.1 (U j)) (hB'.1 (V j)) (hB.2.1 (U j)).continuous
      (hB'.2.1 (V j)).continuous 0
    exact (hK.measurable.mul (hf.comp continuous_quotientDetAbs.measurable)).aestronglyMeasurable
  have hMeas' (j : ℕ) : AEStronglyMeasurable (H j) ν := by
    have hK := continuous_dualKernel h (hB.1 (U j)) (hB'.1 (V j)) (hB.2.1 (U j)).continuous
      (hB'.2.1 (V j)).continuous 0
    exact (hK.measurable.mul (hf'.comp (continuous_quotientDetAbs.measurable.comp measurable_fst))).aestronglyMeasurable
  have hFB (j : ℕ) (q : Q t) : ‖F j q‖ ≤ M q := by
    let x := padGL (Nat.succ_le_succ h.le) q.out
    let y := q.out
    let c := P y (0 - ((r - t : ℕ) : ℂ) / 2) * f (quotientDetAbs q)
    have he : F j q = B (U j) x * B' (V j) y * c := by
      simp only [F, weightedOrdinary, realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, x, y, c, mul_assoc]
    rw [he, hU, hV]
    apply norm_compactAverage_pair_le _ _ (hw j) (hz j) (hw₀ j) (hz₀ j) (hw₁ j) (hz₁ j)
    intro k l
    simpa only [weightedOrdinary, realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
      ArchimedeanLocal.translateFunction, x, y, c, mul_assoc] using hBound q k l
  have hHB (j : ℕ) (p : Q t × R r t) : ‖H j p‖ ≤ M' p := by
    let x := Langlands.GeneralLinear.weylLong (r + 1) ℝ * Langlands.GeneralLinear.inverseTranspose (r + 1) ℝ
      (ArchimedeanLocal.rectangularPoint h p.1.out p.2 * ArchimedeanLocal.unfoldingWeyl h)
    let y := Langlands.GeneralLinear.weylLong (t + 1) ℝ * Langlands.GeneralLinear.inverseTranspose (t + 1) ℝ p.1.out
    let c := P p.1.out (0 - ((r - t : ℕ) : ℂ) / 2) * f' (quotientDetAbs p.1)
    have he : H j p = B (U j) x * B' (V j) y * c := by
      simp only [H, weightedDual, realUnequalDualKernel, ArchimedeanLocal.blockKernel,
        ArchimedeanLocal.translateFunction, ArchimedeanLocal.dualFunction, x, y, c, mul_assoc]
    rw [he, hU, hV]
    apply norm_compactAverage_pair_le _ _ (hw j) (hz j) (hw₀ j) (hz₀ j) (hw₁ j) (hz₁ j)
    intro k l
    simpa only [weightedDual, realUnequalDualKernel, ArchimedeanLocal.blockKernel,
      ArchimedeanLocal.translateFunction, ArchimedeanLocal.dualFunction, x, y, c, mul_assoc] using hBound' p k l
  have hLim : Tendsto (fun j => ∫ q, F j q ∂μ) atTop
      (𝓝 (∫ q, weightedOrdinary h (ρ g (B v)) (ρ g' (B' v')) f q ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence M hMeas hM (fun j => ae_of_all _ (hFB j))
      (ae_of_all _ fun q => ?_)
    unfold F weightedOrdinary realUnequalIntegrand ArchimedeanLocal.unequalIntegrand ArchimedeanLocal.translateFunction
    exact (((hUlim _).mul (hVlim _)).mul tendsto_const_nhds).mul tendsto_const_nhds
  have hLim' : Tendsto (fun j => ∫ p, H j p ∂ν) atTop
      (𝓝 (∫ p, weightedDual h (ρ g (B v)) (ρ g' (B' v')) f' p ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence M' hMeas' hM' (fun j => ae_of_all _ (hHB j))
      (ae_of_all _ fun p => ?_)
    unfold H weightedDual realUnequalDualKernel ArchimedeanLocal.blockKernel
      ArchimedeanLocal.dualFunction ArchimedeanLocal.translateFunction
    exact (((hUlim _).mul (hVlim _)).mul tendsto_const_nhds).mul tendsto_const_nhds
  have he : (fun j => ∫ q, F j q ∂μ) = fun j => ∫ p, H j p ∂ν := funext fun j => hId (U j) (V j)
  rw [he] at hLim
  exact tendsto_nhds_unique hLim hLim'

end Langlands.Global.RankinSelbergGlobal.RealWhittakerTranslatedIntegrals
