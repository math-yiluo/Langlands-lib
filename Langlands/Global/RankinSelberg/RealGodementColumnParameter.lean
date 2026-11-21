import Langlands.Analysis.SchwartzCompactFamilies
import Langlands.Global.RankinSelberg.RealGodementSmoothLeading
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Entire Godement column evaluations with exponential Schwartz test families -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.Analysis.SchwartzCompactFamilies
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Filter MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap ContDiff NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealJacquetFrobenius

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ

/-- The integral of the absolutely convergent column kernel is complex-linear in the test. -/
def columnMellinLinear (μ : Measure G) [μ.IsHaarMeasure] (a : ℝˣ) (W : G → ℂ)
    (hW : ∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W ∈
      RealLocalWhittaker.regularFunctions t (-a))
    (hGrowth : RealUniformWhittaker.HasUniformDerivativeGrowth W)
    (p : ℕ) (s : ℂ) : 𝓢(X, ℂ) →ₗ[ℂ] ℂ := by
  let K (Φ : 𝓢(X, ℂ)) := columnMellinIntegrand a Φ W p s
  have hI (Φ : 𝓢(X, ℂ)) : Integrable (K Φ) μ :=
    (realGodementColumnConvergence t μ a Φ W hW hGrowth p).1 s
  refine { toFun := fun Φ => ∫ h, K Φ h ∂μ, map_add' := ?_, map_smul' := ?_ }
  · intro Φ Ψ
    have hAdd (h : G) : K (Φ + Ψ) h = K Φ h + K Ψ h := by
      simp only [K, columnMellinIntegrand, columnMellinBase, ← firstColumnFourierLinear_apply,
        map_add, add_mul]
    simp_rw [hAdd]
    exact integral_add (hI Φ) (hI Ψ)
  · intro c Φ
    have hSmul (h : G) : K (c • Φ) h = c • K Φ h := by
      simp only [K, columnMellinIntegrand, columnMellinBase, ← firstColumnFourierLinear_apply,
        map_smul, smul_eq_mul]
      ring
    simp_rw [hSmul]
    exact integral_smul c (K Φ)

private theorem norm_columnMellin_integral_le {μ : Measure G} (a : ℝˣ) (W : G → ℂ)
    (p : ℕ) (s : ℂ) (Φ : 𝓢(X, ℂ)) (c : ℝ) {B : G → ℝ}
    (hI : Integrable (columnMellinIntegrand a Φ W p s) μ) (hB : Integrable B μ)
    (hBounds : ∀ h, ‖columnMellinIntegrand a Φ W p s h‖ ≤ c * B h) :
    ‖∫ h, columnMellinIntegrand a Φ W p s h ∂μ‖ ≤ c * ∫ h, B h ∂μ := by
  calc
    _ ≤ ∫ h, ‖columnMellinIntegrand a Φ W p s h‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ h, c * B h ∂μ := integral_mono hI.norm (hB.const_mul c) hBounds
    _ = _ := integral_const_mul _ _

private theorem differentiable_apply_exponential
    (L : ℂ → 𝓢(X, ℂ) →ₗ[ℂ] ℂ)
    (hAnalytic : ∀ Φ, Differentiable ℂ (fun z => L z Φ))
    (hLocal : ∀ z : ℂ, ∃ q : Seminorm ℝ 𝓢(X, ℂ), Continuous q ∧
      ∀ᶠ w in 𝓝 z, ∀ Φ, ‖L w Φ‖ ≤ q Φ)
    (b : X → ℂ) (hb : ContDiff ℝ ∞ b) (Φ : 𝓢(X, ℂ)) (S : Set X) (hS : IsCompact S)
    (hSupport : ∀ x ∉ S, Φ x = 0) :
    Differentiable ℂ (fun z => L z (exponentialTest b hb Φ S hS hSupport z)) := by
  let f := exponentialTest b hb Φ S hS hSupport
  intro z
  obtain ⟨V, hV, hVeq, _⟩ := schwartzCompactExponential X b hb Φ S hS hSupport z
  obtain ⟨q, hq, hBound⟩ := hLocal z
  let l := 𝓝[≠] (0 : ℂ)
  have hAt : Tendsto (fun r : ℂ => z + r) l (𝓝 z) := by
    have hAdd : Continuous (fun r : ℂ => z + r) := continuous_const.add continuous_id
    simpa only [add_zero] using
      (hAdd.continuousAt (x := (0 : ℂ))).tendsto.mono_left nhdsWithin_le_nhds
  have hQ : Tendsto (fun r => q (V r - V 0)) l (𝓝 0) := by
    have hc : Continuous (fun r => q (V r - V 0)) := hq.comp (hV.sub continuous_const)
    simpa only [sub_self, map_zero] using
      (hc.continuousAt (x := (0 : ℂ))).tendsto.mono_left nhdsWithin_le_nhds
  have hSmall : Tendsto (fun r => L (z + r) (V r - V 0)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _)
      ((hAt.eventually hBound).mono fun r hr => hr (V r - V 0)) hQ
  have hVar : Tendsto (fun r => L (z + r) (V r)) l (𝓝 (L z (V 0))) := by
    have hFixed := (hAnalytic (V 0)).continuous.continuousAt (x := z).tendsto.comp hAt
    have hSum := hSmall.add hFixed
    simpa only [Function.comp_apply, map_sub, sub_add_cancel, zero_add] using hSum
  let d := deriv (fun w => L w (f z)) z
  have hBase : Tendsto (fun r => r⁻¹ • (L (z + r) (f z) - L z (f z))) l (𝓝 d) :=
    ((hAnalytic (f z) z).hasDerivAt).tendsto_slope_zero
  apply HasDerivAt.differentiableAt (f' := d + L z (V 0))
  refine hasDerivAt_iff_tendsto_slope_zero.mpr ((hBase.add hVar).congr' ?_)
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℂ)) (s := {(0 : ℂ)}ᶜ)] with r hr
  have hr' : r ≠ 0 := hr
  change r⁻¹ • (L (z + r) (f z) - L z (f z)) + L (z + r) (V r) =
    r⁻¹ • (L (z + r) (f (z + r)) - L z (f z))
  have hSplit : L (z + r) (f (z + r)) - L z (f z) =
      (L (z + r) (f z) - L z (f z)) + r • L (z + r) (V r) := by
    rw [← map_smul, ← hVeq r, map_sub]
    abel
  rw [hSplit, smul_add, inv_smul_smul₀ hr']

/-- Changing only the leading exponent multiplies the determinant weight by an exponential. -/
theorem determinantWeight_exponent_shift {n : ℕ} (p : Fin 2) (s z w : ℂ)
    (g : Langlands.GeneralLinear n ℝ) :
    determinantWeight (charData p z) s g = determinantWeight (charData p w) s g *
      Complex.exp ((z - w) * (Real.log |g.val.det| : ℂ)) := by
  let d := determinant g
  let b : ℂ := (|(d : ℝ)| : ℝ)
  have hb : b ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr d.ne_zero)
  have hLog : Complex.log b = (Real.log |g.val.det| : ℂ) :=
    (Complex.ofReal_log (abs_nonneg _)).symm
  have hExp : b ^ (z - w) = Complex.exp ((z - w) * (Real.log |g.val.det| : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hb, hLog, mul_comm]
  change ((charData p z).character d : ℂ) * b ^ s = ((charData p w).character d : ℂ) * b ^ s * _
  rw [← hExp, (charData p z).character_eq, (charData p w).character_eq]
  change _ ^ p.val * b ^ z * b ^ s = _ ^ p.val * b ^ w * b ^ s * b ^ (z - w)
  have hPow : b ^ z = b ^ w * b ^ (z - w) := by
    rw [← Complex.cpow_add _ _ hb]
    congr 1
    abel
  rw [hPow]
  ring

/-- The leading Godement column value remains entire for compact tests multiplied by a
spectral exponential of any smooth multiplier. -/
def RealGodementColumnParameterStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2)
    (W : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    (∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W ∈
      RealLocalWhittaker.regularFunctions t (-a)) →
    RealUniformWhittaker.HasUniformDerivativeGrowth W →
    ∀ (g : Langlands.GeneralLinear (t + 2) ℝ)
      (b : Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
      (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ))
      (S : Set (Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ)) (hS : IsCompact S)
      (hSupport : ∀ x ∉ S, Φ x = 0),
      Differentiable ℂ (fun z => godementLeadingFamily D a
        (exponentialTest b hb Φ S hS hSupport z) W p g z)

theorem realGodementColumnParameter : RealGodementColumnParameterStatement := by
  intro t D a p W hW hGrowth g b hb Φ S hS hSupport
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let g' := weylLong (t + 2) ℝ * g
  let T := rectangularTranslateCLM (r := t + 1) 1 g'
  let s (z : ℂ) := z + (t : ℂ) / 2
  let L (z : ℂ) := (columnMellinLinear μ a W hW hGrowth p.val (s z)).comp T.toLinearMap
  have hL (f : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ)) :
      Differentiable ℂ (fun z => L z f) :=
    ((realGodementColumnConvergence t μ a (T f) W hW hGrowth p.val).2.comp
      (differentiable_id.add_const _))
  have hLocal (z : ℂ) :
      ∃ q : Seminorm ℝ 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ),
        Continuous q ∧ ∀ᶠ w in 𝓝 z, ∀ f, ‖L w f‖ ≤ q f := by
    let radius := |(s z).re - (t + 1 : ℕ)| + 1
    obtain ⟨q, B, hq, hB, hB₀, hBounds⟩ :=
      realGodementColumnSeminorm t μ a W hW hGrowth radius (by dsimp [radius]; positivity)
    let C : ℝ≥0 := ⟨∫ h, B h ∂μ, integral_nonneg hB₀⟩
    let q' := q.comp ((T.restrictScalars ℝ).toLinearMap)
    refine ⟨C • q', (hq.comp T.continuous).const_mul (C : ℝ), ?_⟩
    have hCont : Continuous (fun w => |(s w).re - (t + 1 : ℕ)|) :=
      ((Complex.continuous_re.comp (continuous_id.add continuous_const)).sub continuous_const).abs
    have hNear := hCont.continuousAt.eventually_lt continuousAt_const
      (show |(s z).re - (t + 1 : ℕ)| < radius by dsimp [radius]; linarith)
    filter_upwards [hNear] with w hw
    intro f
    have hi := (realGodementColumnConvergence t μ a (T f) W hW hGrowth p.val).1 (s w)
    have hI := norm_columnMellin_integral_le a W p.val (s w) (T f) (q (T f)) hi hB
      (hBounds (T f) p.val (s w) hw.le)
    change ‖∫ h, columnMellinIntegrand a (T f) W p.val (s w) h ∂μ‖ ≤
      (∫ h, B h ∂μ) * q (T f)
    simpa only [mul_comm (q (T f))] using hI
  have hDet : Differentiable ℂ (fun z => determinantWeight (charData p z) (((t : ℂ) + 1) / 2) g') := by
    rw [funext fun z => determinantWeight_exponent_shift p _ z 0 g']
    simp only [sub_zero]
    exact ((differentiable_id.mul_const _).cexp).const_mul _
  exact hDet.mul (differentiable_apply_exponential L hL hLocal b hb Φ S hS hSupport)

end Langlands.Global.RankinSelbergGlobal.RealGodement
