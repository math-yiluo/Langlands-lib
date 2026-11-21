import Langlands.Global.RankinSelberg.ComplexBruhatNormalDirection
import Langlands.Global.RankinSelberg.ComplexBruhatVariableDirection
import Langlands.HarmonicAnalysis.Distribution.SmoothNilpotentJetVanishing
import Langlands.HarmonicAnalysis.Distribution.ComplexSmoothTestTransport

/-! # Vanishing in a neighborhood of a non-open complex Bruhat cell -/

noncomputable section

open Set TopologicalSpace
open scoped Classical ContDiff Distributions Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexBruhatCellVanishing

open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.HarmonicAnalysis (fullComplexSmoothTestPullbackCLM fullComplexSmoothTestPullbackCLM_apply
  tsupport_fullComplexSmoothTestPullbackCLM_subset smoothFirstOrderTest smoothFirstOrderTest_apply
  smoothNilpotentJetVanishing)
open ComplexOppositeCompactChart (Coordinates)
open ComplexBruhatGaussChart (cellCoordinates)
open ComplexBruhatTestExtension (ChartTest)
open ComplexBruhatChartDerivative (chartDerivativeTest chartVector chartScalar)
open ComplexBruhatStabilizer (TangentCoordinates NormalCoordinates splitCoordinates cellPoint
  mem_cellCoordinates_iff_snd_eq_zero)
open ComplexBruhatNormalDirection (splitChartVector contDiff_varying_chartScalar complexBruhatNormalDirection)
open ComplexBruhatVariableDirection (complexBruhatVariableDirection frequencyLinear)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ

/-- A distribution satisfying the Whittaker equations and supported inside a lower Bruhat
cell on an open coordinate neighborhood vanishes throughout that neighborhood. -/
def ComplexBruhatCellVanishingStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ) (w : Equiv.Perm (Fin (r + 1))),
    (¬ StrictAnti w) → ∀ (T : ChartTest (r + 1) →L[ℂ] ℂ),
    (∀ (Y : Mat (r + 1)), (∀ i j, j ≤ i → Y i j = 0) → ∀ φ : ChartTest (r + 1),
      T (chartDerivativeTest w ds Y φ) = complexWhittakerFrequency a Y * T φ) →
    ∀ O : Opens (Coordinates (r + 1)),
      Distribution.IsVanishingOn (⇑T) ((O : Set (Coordinates (r + 1))) \ cellCoordinates w) →
      Distribution.IsVanishingOn (⇑T) (O : Set (Coordinates (r + 1)))

set_option maxHeartbeats 1100000 in
theorem complexBruhatCellVanishing : ComplexBruhatCellVanishingStatement := by
  intro r ds a w hw T hT O hSupp
  let e := splitCoordinates w
  let P := TangentCoordinates w × NormalCoordinates w
  let O' : Opens P := ⟨e.symm ⁻¹' (O : Set (Coordinates (r + 1))), O.isOpen.preimage e.symm.continuous⟩
  let includeTest : 𝓓(O', ℂ) →L[ℂ] 𝓓((⊤ : Opens P), ℂ) := TestFunction.monoCLM ℂ
  have hInclude (f : 𝓓(O', ℂ)) : (includeTest f : P → ℂ) = ⇑f := by simp [includeTest]
  let liftTest : 𝓓(O', ℂ) →L[ℂ] ChartTest (r + 1) :=
    (fullComplexSmoothTestPullbackCLM e).comp includeTest
  have hLift (f : 𝓓(O', ℂ)) (z : Coordinates (r + 1)) : liftTest f z = f (e z) := by
    simp only [liftTest, ContinuousLinearMap.comp_apply, fullComplexSmoothTestPullbackCLM_apply]
    exact congrFun (hInclude f) (e z)
  let T' : 𝓓(O', ℂ) →L[ℂ] ℂ := T.comp liftTest
  have hSupp' : Distribution.IsVanishingOn (⇑T') {p : P | p.2 ≠ 0} := by
    intro f hf
    apply hSupp
    intro z hz
    have h := tsupport_fullComplexSmoothTestPullbackCLM_subset e (includeTest f) hz
    change e z ∈ tsupport (includeTest f) at h
    rw [hInclude] at h
    have hz0 : z ∉ cellCoordinates w := fun hc => hf h ((mem_cellCoordinates_iff_snd_eq_zero w z).mp hc)
    have hO := f.tsupport_subset h
    change e.symm (e z) ∈ O at hO
    rw [e.symm_apply_apply] at hO
    exact ⟨hO, hz0⟩
  obtain ⟨X, hX, hV, hXData⟩ := complexBruhatNormalDirection r ds a w hw
  let Z (z : Coordinates (r + 1)) := X (e z).1
  have hZ : ContDiff ℝ ∞ Z := hX.comp (contDiff_fst.comp e.contDiff)
  obtain ⟨c, A, hC, hA, hFormula⟩ := complexBruhatVariableDirection r ds a w T hT Z hZ
    (fun z => (hXData (e z).1).1)
  let V : P → P := splitChartVector w X
  let b (p : P) := chartScalar w ds (X p.1) (e.symm p) + (c (e.symm p) : ℂ) - complexWhittakerFrequency a (X p.1)
  have hb : ContDiff ℝ ∞ b := ((contDiff_varying_chartScalar w ds e.symm.contDiff
    (hX.comp contDiff_fst)).add (Complex.ofRealCLM.contDiff.comp (hC.comp e.symm.contDiff))).sub
      ((frequencyLinear a (r := r)).toContinuousLinearMap.contDiff.comp (hX.comp contDiff_fst))
  have hV0 (x : TangentCoordinates w) : V (x, 0) = 0 := (hXData x).2.2.1
  have hN (x : TangentCoordinates w) : Langlands.HarmonicAnalysis.productNormalDerivative V x ^ 3 = 0 :=
    (hXData x).2.2.2.2
  have hb0 (x : TangentCoordinates w) : b (x, 0) ≠ 0 := by
    have h : b (x, 0) = (c (cellPoint w x) : ℂ) - ((4 * Real.pi : ℝ) : ℂ) * Complex.I := by
      change chartScalar w ds (X x) (cellPoint w x) + (c (cellPoint w x) : ℂ) -
        complexWhittakerFrequency a (X x) = _
      rw [(hXData x).2.2.2.1, (hXData x).2.1, zero_add]
    intro hz
    have he := congrArg Complex.im (h.symm.trans hz)
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, Complex.zero_im, zero_sub, neg_eq_zero] at he
    exact (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero) he
  let op := smoothFirstOrderTest (Ω := O') (fun _ => (1 : ℂ)) b V contDiff_const hb hV
  have hOp (f : 𝓓(O', ℂ)) : T' (op f) = 0 := by
    have hPull : (liftTest f : Coordinates (r + 1) → ℂ) = (⇑f) ∘ e := funext (hLift f)
    have hDeriv (z : Coordinates (r + 1)) :
        fderiv ℝ (liftTest f) z (chartVector w (Z z) z) = fderiv ℝ f (e z) (V (e z)) := by
      rw [hPull, fderiv_comp z (f.contDiff.differentiable (by simp) (e z)) e.toContinuousLinearMap.differentiableAt,
        show fderiv ℝ (⇑e) z = e.toContinuousLinearMap from e.toContinuousLinearMap.fderiv]
      change fderiv ℝ f (e z) (e (chartVector w (Z z) z)) = fderiv ℝ f (e z) (V (e z))
      rw [show V (e z) = e (chartVector w (Z z) z) by
        change e (chartVector w (X (e z).1) (e.symm (e z))) = _
        rw [e.symm_apply_apply]]
    have hScalar (z : Coordinates (r + 1)) :
        b (e z) = chartScalar w ds (Z z) z + (c z : ℂ) - complexWhittakerFrequency a (Z z) := by
      dsimp only [b, Z]
      rw [e.symm_apply_apply]
    have hEq : liftTest (op f) = A (liftTest f) := by
      ext z
      rw [hLift, hFormula, hDeriv, ← hScalar, hLift]
      simp only [op, smoothFirstOrderTest_apply, one_mul]
    change T (liftTest (op f)) = 0
    rw [hEq]
    exact hA (liftTest f)
  let q (p : P) := (b (p.1, 0))⁻¹
  have hq : ContDiff ℝ ∞ q := (hb.comp (contDiff_fst.prodMk contDiff_const)).inv fun p => hb0 p.1
  let u (p : P) := fderiv ℝ q p (V p) + b p * q p - 1
  have hu : ContDiff ℝ ∞ u := (((hq.fderiv_right (by simp)).clm_apply hV).add (hb.mul hq)).sub contDiff_const
  have hu0 (x : TangentCoordinates w) : u (x, 0) = 0 := by
    change fderiv ℝ q (x, 0) (V (x, 0)) + b (x, 0) * (b (x, 0))⁻¹ - 1 = 0
    rw [hV0, map_zero, mul_inv_cancel₀ (hb0 x), zero_add, sub_self]
  let D := smoothFirstOrderTest (Ω := O') q u V hq hu hV
  have hId (f : 𝓓(O', ℂ)) : T' (f + D f) = 0 := by
    let g := smoothFirstOrderTest (Ω := O') (fun _ => (0 : ℂ)) q V contDiff_const hq hV f
    have hg : (g : P → ℂ) = fun p => q p * f p := by
      funext p
      simp only [g, smoothFirstOrderTest_apply, zero_mul, zero_add]
    have hEq : op g = f + D f := by
      ext p
      simp only [op, D, smoothFirstOrderTest_apply, one_mul, add_apply]
      rw [hg, fderiv_fun_mul (hq.differentiable (by simp) p) (f.contDiff.differentiable (by simp) p)]
      simp only [add_apply, smul_apply, smul_eq_mul, u]
      ring
    rw [← hEq]
    exact hOp g
  have hZero : T' = 0 := smoothNilpotentJetVanishing T' hSupp' q u V hq hu hV 3 hV0 hu0 hN hId
  intro ψ hψ
  let h := fullComplexSmoothTestPullbackCLM e.symm ψ
  have hO' : tsupport h ⊆ (O' : Set P) :=
    (tsupport_fullComplexSmoothTestPullbackCLM_subset e.symm ψ).trans fun _ hp => hψ hp
  let f : 𝓓(O', ℂ) := ⟨h, h.contDiff, h.hasCompactSupport, hO'⟩
  have he : liftTest f = ψ := by
    ext z
    rw [hLift]
    change fullComplexSmoothTestPullbackCLM e.symm ψ (e z) = ψ z
    rw [fullComplexSmoothTestPullbackCLM_apply, e.symm_apply_apply]
  have hEval : T (liftTest f) = 0 := by rw [← show T' f = T (liftTest f) from rfl, hZero, zero_apply]
  exact he ▸ hEval

end Langlands.Global.RankinSelbergGlobal.ComplexBruhatCellVanishing
