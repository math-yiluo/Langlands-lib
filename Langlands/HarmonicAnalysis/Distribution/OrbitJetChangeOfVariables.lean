import Langlands.HarmonicAnalysis.Distribution.ProductJetTransform
import Langlands.HarmonicAnalysis.Distribution.ZeroNormalOrbitChart
import Mathlib.MeasureTheory.Function.Jacobian

/-! # Change of orbit variables for leading normal jets -/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

variable {O Z N F : Type*}
  [NormedAddCommGroup O] [NormedSpace ℝ O]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "Coord" => ((O × Z) × N)
local notation "Jet[" i "]" => (N [×i]→L[ℝ] F)

private theorem contDiffOn_productNormalDerivative_of_chart {Ψ : OpenPartialHomeomorph Coord Coord}
    (hs : ContDiffOn ℝ ∞ Ψ Ψ.source) :
    ContDiffOn ℝ ∞ (productNormalDerivative Ψ) {p | (p, 0) ∈ Ψ.source} := by
  let pre := (ContinuousLinearMap.compL ℝ N Coord Coord).flip (ContinuousLinearMap.inr ℝ (O × Z) N)
  let post := ContinuousLinearMap.compL ℝ N Coord N (ContinuousLinearMap.snd ℝ (O × Z) N)
  exact (post.comp pre).contDiff.comp_contDiffOn
    ((hs.fderiv_of_isOpen Ψ.open_source (by simp)).comp
      (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hp => hp))

/-- A leading normal jet transforms by multilinear pullback and the ratio of
its original weight to the absolute Jacobian in the orbit variable. -/
def orbitJetTransportKernel (Ψ : OpenPartialHomeomorph Coord Coord) (w : Coord → ℝ)
    (i : ℕ) (p : Z × O) : Jet[i] →L[ℝ] Jet[i] :=
  let q := (Ψ.symm ((p.2, p.1), 0)).1
  (w (q, 0) / zeroNormalOrbitJacobian Ψ q) •
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i => productNormalDerivative Ψ q)

@[simp]
theorem orbitJetTransportKernel_apply (Ψ : OpenPartialHomeomorph Coord Coord) (w : Coord → ℝ)
    (i : ℕ) (z : Z) (t : O) (a : Jet[i]) (v : Fin i → N) :
    orbitJetTransportKernel Ψ w i (z, t) a v =
      let q := (Ψ.symm ((t, z), 0)).1
      (w (q, 0) / zeroNormalOrbitJacobian Ψ q) • a (fun k => productNormalDerivative Ψ q (v k)) := rfl

theorem contDiffOn_orbitJetTransportKernel [FiniteDimensional ℝ O]
    {Ψ : OpenPartialHomeomorph Coord Coord} (hs : ContDiffOn ℝ ∞ Ψ Ψ.source)
    (hi : ContDiffOn ℝ ∞ Ψ.symm Ψ.target)
    (hΨ : PreservesZeroNormalFibers Ψ) (hΨi : PreservesZeroNormalFibers Ψ.symm)
    {w : Coord → ℝ} (hw : ContDiffOn ℝ ∞ w Ψ.source) (i : ℕ) :
    ContDiffOn ℝ ∞ (orbitJetTransportKernel (F := F) Ψ w i)
      {p : Z × O | ((p.2, p.1), 0) ∈ Ψ.target} := by
  let s : Set (O × Z) := {p | (p, 0) ∈ Ψ.source}
  let t : Set (Z × O) := {p | ((p.2, p.1), 0) ∈ Ψ.target}
  let j (p : Z × O) : Coord := ((p.2, p.1), 0)
  let q (p : Z × O) : O × Z := (Ψ.symm (j p)).1
  have hj : ContDiff ℝ ∞ j := (contDiff_snd.prodMk contDiff_fst).prodMk contDiff_const
  have hq : ContDiffOn ℝ ∞ q t := (hi.comp hj.contDiffOn (fun _ hp => hp)).fst
  have hqs : MapsTo q t s := by
    intro p hp
    have h := hΨi (p.2, p.1) hp
    change (q p, 0) ∈ Ψ.source
    rw [show (q p, 0) = Ψ.symm (j p) from Prod.ext rfl (congrArg Prod.snd h).symm]
    exact Ψ.map_target hp
  have hd : ContDiffOn ℝ ∞ (zeroNormalOrbitJacobian Ψ) s :=
    contDiffOn_zeroNormalOrbitJacobian hs hi hΨ hΨi
  have hr : ContDiffOn ℝ ∞ (fun p : O × Z => w (p, 0) / zeroNormalOrbitJacobian Ψ p) s :=
    (hw.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hp => hp)).div hd
      (fun _ hp => (zeroNormalOrbitJacobian_pos hs hi hΨ hΨi hp).ne')
  have hL : ContDiffOn ℝ ∞
      (fun p : O × Z => fun _ : Fin i => productNormalDerivative Ψ p) s :=
    contDiffOn_pi.mpr (fun _ => contDiffOn_productNormalDerivative_of_chart hs)
  let op := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin i => N) (fun _ : Fin i => N) F
  exact ((hr.smul (op.contDiff.comp_contDiffOn hL)).comp hq hqs)

/-- The orbit change of variables for a weighted leading jet. The denominator
of the transported weight cancels the orbit Jacobian from the substitution. -/
theorem integral_orbitJetTransportKernel [FiniteDimensional ℝ O] [MeasurableSpace O] [BorelSpace O]
    (μ : Measure O) [μ.IsAddHaarMeasure]
    {Ψ : OpenPartialHomeomorph Coord Coord} (hs : ContDiffOn ℝ ∞ Ψ Ψ.source)
    (hi : ContDiffOn ℝ ∞ Ψ.symm Ψ.target)
    (hΨ : PreservesZeroNormalFibers Ψ) (hΨi : PreservesZeroNormalFibers Ψ.symm)
    (w : Coord → ℝ) (i : ℕ) (z : Z) (χ : O → ℝ) (a : Jet[i]) :
    let e := zeroNormalOrbitChart Ψ hΨ hΨi z
    (∫ t in e.target, χ t • orbitJetTransportKernel Ψ w i (z, t) a ∂μ) =
      ∫ t in e.source, (χ (e t) * w ((t, z), 0)) •
        a.compContinuousLinearMap (fun _ => productNormalDerivative Ψ (t, z)) ∂μ := by
  let e := zeroNormalOrbitChart Ψ hΨ hΨi z
  change (∫ t in e.target, χ t • orbitJetTransportKernel Ψ w i (z, t) a ∂μ) = _
  rw [integral_target_eq_integral_abs_det_fderiv_smul μ
    (fun t ht => hasFDerivAt_zeroNormalOrbitChart hs hΨ hΨi z ht)]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro t ht
  have hforward : Ψ ((t, z), 0) = ((e t, z), 0) := hΨ (t, z) ht
  have hback : (Ψ.symm ((e t, z), 0)).1 = (t, z) := by
    rw [← hforward, Ψ.left_inv ht]
  have hn := (zeroNormalOrbitJacobian_pos hs hi hΨ hΨi (p := (t, z)) ht).ne'
  change zeroNormalOrbitJacobian Ψ (t, z) •
    (χ (e t) • orbitJetTransportKernel Ψ w i (z, e t) a) = _
  rw [orbitJetTransportKernel, hback, smul_apply, smul_smul, smul_smul]
  congr 1
  field_simp [hn]
  ring

end Langlands.HarmonicAnalysis
