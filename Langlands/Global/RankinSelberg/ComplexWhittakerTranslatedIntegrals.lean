import Langlands.Global.RankinSelberg.ComplexWhittakerRightTranslateApproximation
import Langlands.Global.RankinSelberg.ComplexUnequalMellinReduction
import Langlands.Global.RankinSelberg.ComplexUnequalFamilyKernels
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Weighted unequal-rank identities on complex Whittaker right translates -/

noncomputable section

open MeasureTheory Filter
open scoped Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexWhittakerTranslatedIntegrals

open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal
open ComplexGodement (compactMatrixHaar)
open ComplexUnequalFamily (HasLeftCharacter continuous_ordinaryKernel continuous_dualKernel)
open ComplexUnequalMellinReduction (quotientDetAbs continuous_quotientDetAbs)
open ComplexWhittakerRightTranslateApproximation (complexWhittakerRightTranslateApproximation)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "KU" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "Std" => Automorphic.complexStandardKFinite
local notation "R" => fun r t => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ
local notation "ρ" => ArchimedeanLocal.translateFunction
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

local instance translatedIntegralsUnitaryMeasurable (n : ℕ) : MeasurableSpace (KU n) := borel _
local instance translatedIntegralsUnitaryBorel (n : ℕ) : BorelSpace (KU n) := ⟨rfl⟩

private theorem norm_compactAverage_le {n : ℕ} (w : KU n → ℝ) (fw : Continuous w)
    (hPos : ∀ k, 0 ≤ w k) (hMass : (∫ k, w k ∂compactMatrixHaar n) = 1)
    (f : KU n → ℂ) (M : ℝ) (h : ∀ k, ‖f k‖ ≤ M) :
    ‖∫ k, (w k : ℂ) * f k ∂compactMatrixHaar n‖ ≤ M := by
  have hI : Integrable w (compactMatrixHaar n) :=
    fw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace w)
  calc
    _ ≤ ∫ k, w k * M ∂compactMatrixHaar n := by
      apply norm_integral_le_of_norm_le (hI.mul_const M)
      exact ae_of_all _ fun k => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hPos k)]
        exact mul_le_mul_of_nonneg_left (h k) (hPos k)
    _ = M := by rw [integral_mul_const, hMass, one_mul]

private theorem norm_compactAverage_pair_le {n m : ℕ} (w : KU n → ℝ) (v : KU m → ℝ)
    (hw : Continuous w) (hv : Continuous v) (hw₀ : ∀ k, 0 ≤ w k) (hv₀ : ∀ k, 0 ≤ v k)
    (hw₁ : (∫ k, w k ∂compactMatrixHaar n) = 1) (hv₁ : (∫ k, v k ∂compactMatrixHaar m) = 1)
    (F : KU n → ℂ) (H : KU m → ℂ) (c : ℂ) (M : ℝ)
    (h : ∀ k l, ‖F k * H l * c‖ ≤ M) :
    ‖(∫ k, (w k : ℂ) * F k ∂compactMatrixHaar n) *
      (∫ l, (v l : ℂ) * H l ∂compactMatrixHaar m) * c‖ ≤ M := by
  let y := ∫ l, (v l : ℂ) * H l ∂compactMatrixHaar m
  have hy (k : KU n) : ‖F k * y * c‖ ≤ M := by
    have he : F k * y * c = ∫ l, (v l : ℂ) * (F k * H l * c) ∂compactMatrixHaar m := by
      dsimp only [y]
      rw [← integral_const_mul, ← integral_mul_const]
      apply integral_congr_ae
      exact ae_of_all _ fun l => by dsimp only; ring
    rw [he]
    exact norm_compactAverage_le v hv hv₀ hv₁ (fun l => F k * H l * c) M (h k)
  change ‖(∫ k, (w k : ℂ) * F k ∂compactMatrixHaar n) * y * c‖ ≤ M
  rw [← integral_mul_const, ← integral_mul_const]
  simpa only [mul_assoc] using norm_compactAverage_le w hw hw₀ hw₁ (fun k => F k * y * c) M hy

private theorem hasLeftCharacter_of_model {r : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r ds a) : HasLeftCharacter a W.val := by
  intro u g
  exact complexWhittakerModel_left_equivariant W.2 _ u.2 _

/-- Ordinary and dual weighted integrands use the same quotient determinant weight. -/
def weightedOrdinary {r t : ℕ} (h : t < r) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (f : ℝ → ℂ) (q : Q t) : ℂ := complexUnequalIntegrand h W V 0 q * f (quotientDetAbs q)

def weightedDual {r t : ℕ} (h : t < r) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (f : ℝ → ℂ) (p : Q t × R r t) : ℂ := complexUnequalDualKernel h W V 0 p * f (quotientDetAbs p.1)

/-- A weighted integral identity on exact finite vectors extends to their right translates
when each compact family of the two translated kernels has a common integrable bound. -/
def ComplexWhittakerTranslatedIntegralsStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es : List ComplexCharacterData) (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (f f' : ℝ → ℂ), Measurable f → Measurable f' →
    (∀ (U : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a)),
      (∫ q, weightedOrdinary h U.val V.val f q ∂D.measure) =
        ∫ p, weightedDual h U.val V.val f' p ∂complexUnequalDualMeasure (r := r) a D) →
    ∀ (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)) (B' : Std (t + 1) es →ₗ[ℂ] (G (t + 1) → ℂ)),
      IsComplexWhittakerIntertwiner r ds a B → IsComplexWhittakerIntertwiner t es (-a) B' →
    ∀ (v : Std (r + 1) ds) (v' : Std (t + 1) es) (g : G (r + 1)) (g' : G (t + 1))
      (M : Q t → ℝ) (M' : Q t × R r t → ℝ),
      Integrable M D.measure → Integrable M' (complexUnequalDualMeasure (r := r) a D) →
      (∀ q (k : KU (r + 1)) (l : KU (t + 1)),
        ‖weightedOrdinary h (ρ (Unitary.toUnits k * g) (B v)) (ρ (Unitary.toUnits l * g') (B' v')) f q‖ ≤ M q) →
      (∀ p (k : KU (r + 1)) (l : KU (t + 1)),
        ‖weightedDual h (ρ (Unitary.toUnits k * g) (B v)) (ρ (Unitary.toUnits l * g') (B' v')) f' p‖ ≤ M' p) →
      (∫ q, weightedOrdinary h (ρ g (B v)) (ρ g' (B' v')) f q ∂D.measure) =
        ∫ p, weightedDual h (ρ g (B v)) (ρ g' (B' v')) f' p ∂complexUnequalDualMeasure (r := r) a D

set_option maxHeartbeats 1300000 in
theorem complexWhittakerTranslatedIntegrals : ComplexWhittakerTranslatedIntegralsStatement := by
  intro r t h ds es a D f f' hf hf' hId B B' hB hB' v v' g g' M M' hM hM' hBound hBound'
  obtain ⟨U, w, hw, hw₀, hw₁, hU, hUlim⟩ := complexWhittakerRightTranslateApproximation r ds a B hB v g
  obtain ⟨V, z, hz, hz₀, hz₁, hV, hVlim⟩ := complexWhittakerRightTranslateApproximation t es (-a) B' hB' v' g'
  let μ := D.measure
  let ν := complexUnequalDualMeasure (r := r) a D
  let F j := weightedOrdinary h (U j).val (V j).val f
  let H j := weightedDual h (U j).val (V j).val f'
  have hMeas (j : ℕ) : AEStronglyMeasurable (F j) μ := by
    have hK := continuous_ordinaryKernel h (hasLeftCharacter_of_model (U j))
      (hasLeftCharacter_of_model (V j)) (contMDiff_of_mem_complexWhittakerModel (U j).2).continuous
      (contMDiff_of_mem_complexWhittakerModel (V j).2).continuous 0
    exact (hK.measurable.mul (hf.comp continuous_quotientDetAbs.measurable)).aestronglyMeasurable
  have hMeas' (j : ℕ) : AEStronglyMeasurable (H j) ν := by
    have hK := continuous_dualKernel h (hasLeftCharacter_of_model (U j))
      (hasLeftCharacter_of_model (V j)) (contMDiff_of_mem_complexWhittakerModel (U j).2).continuous
      (contMDiff_of_mem_complexWhittakerModel (V j).2).continuous 0
    exact (hK.measurable.mul (hf'.comp (continuous_quotientDetAbs.measurable.comp measurable_fst))).aestronglyMeasurable
  have hFB (j : ℕ) (q : Q t) : ‖F j q‖ ≤ M q := by
    let x := padGL (Nat.succ_le_succ h.le) q.out
    let y := q.out
    let c := P y (0 - ((r - t : ℕ) : ℂ) / 2) * f (quotientDetAbs q)
    have he : F j q = (U j).val x * (V j).val y * c := by
      simp only [F, weightedOrdinary, complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, x, y, c, mul_assoc]
    rw [he, hU, hV]
    apply norm_compactAverage_pair_le _ _ (hw j) (hz j) (hw₀ j) (hz₀ j) (hw₁ j) (hz₁ j)
    intro k l
    simpa only [weightedOrdinary, complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
      ArchimedeanLocal.translateFunction, x, y, c, mul_assoc] using hBound q k l
  have hHB (j : ℕ) (p : Q t × R r t) : ‖H j p‖ ≤ M' p := by
    let x := Langlands.GeneralLinear.weylLong (r + 1) ℂ * Langlands.GeneralLinear.inverseTranspose (r + 1) ℂ
      (ArchimedeanLocal.rectangularPoint h p.1.out p.2 * ArchimedeanLocal.unfoldingWeyl h)
    let y := Langlands.GeneralLinear.weylLong (t + 1) ℂ * Langlands.GeneralLinear.inverseTranspose (t + 1) ℂ p.1.out
    let c := P p.1.out (0 - ((r - t : ℕ) : ℂ) / 2) * f' (quotientDetAbs p.1)
    have he : H j p = (U j).val x * (V j).val y * c := by
      simp only [H, weightedDual, complexUnequalDualKernel, ArchimedeanLocal.blockKernel,
        ArchimedeanLocal.translateFunction, ArchimedeanLocal.dualFunction, x, y, c, mul_assoc]
    rw [he, hU, hV]
    apply norm_compactAverage_pair_le _ _ (hw j) (hz j) (hw₀ j) (hz₀ j) (hw₁ j) (hz₁ j)
    intro k l
    simpa only [weightedDual, complexUnequalDualKernel, ArchimedeanLocal.blockKernel,
      ArchimedeanLocal.translateFunction, ArchimedeanLocal.dualFunction, x, y, c, mul_assoc] using hBound' p k l
  have hLim : Tendsto (fun j => ∫ q, F j q ∂μ) atTop
      (𝓝 (∫ q, weightedOrdinary h (ρ g (B v)) (ρ g' (B' v')) f q ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence M hMeas hM (fun j => ae_of_all _ (hFB j))
      (ae_of_all _ fun q => ?_)
    unfold F weightedOrdinary complexUnequalIntegrand ArchimedeanLocal.unequalIntegrand ArchimedeanLocal.translateFunction
    exact (((hUlim _).mul (hVlim _)).mul tendsto_const_nhds).mul tendsto_const_nhds
  have hLim' : Tendsto (fun j => ∫ p, H j p ∂ν) atTop
      (𝓝 (∫ p, weightedDual h (ρ g (B v)) (ρ g' (B' v')) f' p ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence M' hMeas' hM' (fun j => ae_of_all _ (hHB j))
      (ae_of_all _ fun p => ?_)
    unfold H weightedDual complexUnequalDualKernel ArchimedeanLocal.blockKernel
      ArchimedeanLocal.dualFunction ArchimedeanLocal.translateFunction
    exact (((hUlim _).mul (hVlim _)).mul tendsto_const_nhds).mul tendsto_const_nhds
  have he : (fun j => ∫ q, F j q ∂μ) = fun j => ∫ p, H j p ∂ν := funext fun j => hId (U j) (V j)
  rw [he] at hLim
  exact tendsto_nhds_unique hLim hLim'

end Langlands.Global.RankinSelbergGlobal.ComplexWhittakerTranslatedIntegrals
