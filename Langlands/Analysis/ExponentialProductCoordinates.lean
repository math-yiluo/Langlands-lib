import Langlands.Analysis.LocalSmoothInverse
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Differentiation in exponential product coordinates -/

noncomputable section
set_option autoImplicit false

open scoped ContDiff RightActions

namespace Langlands.Analysis

variable {E N A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local notation "W" => (E × N × ℝ)

/-- The factor formed from the exponential coordinate and the other normal coordinates. -/
def exponentialNormalFactor (X : A) (m : N →L[ℝ] A) (z : W) : A :=
  NormedSpace.exp (z.2.2 • X) * (1 + m z.2.1)

/-- Multiply the exponential normal factor by a function of the tangent coordinates. -/
def exponentialProduct (X : A) (m : N →L[ℝ] A) (b : E → A) (z : W) : A :=
  exponentialNormalFactor X m z * b z.1

theorem contDiff_exponentialNormalFactor (X : A) (m : N →L[ℝ] A) :
    ContDiff ℝ ∞ (exponentialNormalFactor (E := E) X m) := by
  have he : AnalyticOnNhd ℝ (NormedSpace.exp : A → A) Set.univ := fun a _ =>
    NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) a
      (by rw [NormedSpace.expSeries_radius_eq_top, Metric.mem_eball]; exact edist_lt_top _ _)
  have ht : ContDiff ℝ ∞ (fun z : W => z.2.2 • X) :=
    contDiff_snd.snd.smul contDiff_const
  have hm : ContDiff ℝ ∞ (fun z : W => 1 + m z.2.1) :=
    contDiff_const.add (m.contDiff.comp contDiff_snd.fst)
  exact (he.contDiff.comp ht).mul hm

theorem contDiff_exponentialProduct (X : A) (m : N →L[ℝ] A) {b : E → A}
    (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (exponentialProduct X m b) :=
  (contDiff_exponentialNormalFactor X m).mul (hb.comp contDiff_fst)

theorem hasFDerivAt_exponentialNormalFactor (X : A) (m : N →L[ℝ] A) (L : W →L[ℝ] A)
    (hL : ∀ z, L z = z.2.2 • X + m z.2.1) :
    HasFDerivAt (exponentialNormalFactor X m) L 0 := by
  let t := (ContinuousLinearMap.snd ℝ N ℝ).comp (ContinuousLinearMap.snd ℝ E (N × ℝ))
  let v := m.comp ((ContinuousLinearMap.fst ℝ N ℝ).comp (ContinuousLinearMap.snd ℝ E (N × ℝ)))
  let a : ℝ →L[ℝ] A := ContinuousLinearMap.toSpanSingleton ℝ X
  have hs : HasFDerivAt (fun s : ℝ => NormedSpace.exp (s • X)) a (t 0) := by
    rw [map_zero]
    simpa only [a, zero_smul, NormedSpace.exp_zero, one_mul] using!
      (hasDerivAt_exp_smul_const X (0 : ℝ)).hasFDerivAt
  have hd : HasFDerivAt (fun z : W => NormedSpace.exp (t z • X)) (a.comp t) 0 :=
    hs.comp (0 : W) t.hasFDerivAt
  have hp := hd.mul' ((v.hasFDerivAt (x := (0 : W))).const_add (1 : A))
  have he : L = NormedSpace.exp (t 0 • X) •> v + a.comp t <• (1 + v 0) := by
    apply ContinuousLinearMap.ext
    intro z
    change L z = NormedSpace.exp (t 0 • X) * v z + (t z • X) * (1 + v 0)
    rw [map_zero, map_zero, zero_smul, NormedSpace.exp_zero, one_mul, add_zero, mul_one, add_comm]
    exact hL z
  rw [he]
  exact hp

/-- The derivative at zero after adjoining smooth tangent coordinates. -/
theorem hasFDerivAt_exponentialProduct (X : A) (m : N →L[ℝ] A)
    {b : E → A} {D : E →L[ℝ] A} (hb : HasFDerivAt b D 0) (L : W →L[ℝ] A)
    (hL : ∀ z, L z = D z.1 + (z.2.2 • X + m z.2.1) * b 0) :
    HasFDerivAt (exponentialProduct X m b) L 0 := by
  let π := ContinuousLinearMap.fst ℝ E (N × ℝ)
  let t := (ContinuousLinearMap.snd ℝ N ℝ).comp (ContinuousLinearMap.snd ℝ E (N × ℝ))
  let v := m.comp ((ContinuousLinearMap.fst ℝ N ℝ).comp (ContinuousLinearMap.snd ℝ E (N × ℝ)))
  let d := t.smulRight X + v
  have hn := hasFDerivAt_exponentialNormalFactor X m d (fun _ => rfl)
  have hb₀ : HasFDerivAt b D (π (0 : W)) := by
    rw [map_zero]
    exact hb
  have ht := hb₀.comp (0 : W) π.hasFDerivAt
  have hp := hn.mul' ht
  have he : L = exponentialNormalFactor X m (0 : W) •> D.comp π + d <• b (π 0) := by
    apply ContinuousLinearMap.ext
    intro z
    rw [hL]
    change D z.1 + (z.2.2 • X + m z.2.1) * b 0 =
      exponentialNormalFactor X m (0 : W) * D z.1 + (z.2.2 • X + m z.2.1) * b (π 0)
    simp [exponentialNormalFactor]
  rw [he]
  exact hp

/-- An invertible derivative at zero gives a smooth local chart for
the exponential product. The linear equivalence may be constructed
algebraically in finite dimension. -/
theorem exists_exponentialProductChart [FiniteDimensional ℝ E] [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ A] (X : A) (m : N →L[ℝ] A)
    {b : E → A} (hb : ContDiff ℝ ∞ b)
    (L : W ≃ₗ[ℝ] A)
    (hL : ∀ z, L z = fderiv ℝ b 0 z.1 + (z.2.2 • X + m z.2.1) * b 0) :
    ∃ e : OpenPartialHomeomorph W A,
      (e : W → A) = exponentialProduct X m b ∧
      0 ∈ e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have : CompleteSpace W := FiniteDimensional.complete ℝ W
  exact exists_localSmoothInverse (contDiff_exponentialProduct X m hb)
    (hasFDerivAt_exponentialProduct X m (hb.differentiable (by simp) 0).hasFDerivAt
      (L.toContinuousLinearEquiv : W →L[ℝ] A) hL)

/-- After multiplying by a smooth map of the tangent coordinates, the
derivative in the last coordinate is left multiplication by `X`. -/
theorem fderiv_exponentialProduct_last (X : A) (m : N →L[ℝ] A) {b : E → A}
    (hb : ContDiff ℝ ∞ b) (z : W) :
    fderiv ℝ (exponentialProduct X m b) z (0, 0, 1) = X * exponentialProduct X m b z := by
  let f := exponentialProduct X m b
  let c : ℝ → W := fun t => (z.1, z.2.1, t)
  have hc : HasDerivAt c (0, 0, 1) z.2.2 :=
    (hasDerivAt_const z.2.2 z.1).prodMk
      ((hasDerivAt_const z.2.2 z.2.1).prodMk (hasDerivAt_id z.2.2))
  have hp : HasDerivAt (f ∘ c) (X * f z) z.2.2 := by
    have hd := ((hasDerivAt_exp_smul_const' X z.2.2).mul_const (1 + m z.2.1)).mul_const (b z.1)
    change HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * (1 + m z.2.1) * b z.1)
      (X * (NormedSpace.exp (z.2.2 • X) * (1 + m z.2.1) * b z.1)) z.2.2
    simpa only [mul_assoc] using hd
  have hdiff : ContDiff ℝ ∞ f := contDiff_exponentialProduct X m hb
  have hderiv : HasFDerivAt f (fderiv ℝ f z) (c z.2.2) :=
    (hdiff.differentiable (by simp) z).hasFDerivAt
  exact (hderiv.comp_hasDerivAt z.2.2 hc).unique hp

end Langlands.Analysis
