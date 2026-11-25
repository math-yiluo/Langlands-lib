import Langlands.Analysis.ContinuousKernelTraceClassFactorization
import Langlands.Analysis.TorusFourierKernelFactorization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Trace class for compact kernels with a smooth finite-dimensional extension -/

noncomputable section

open MeasureTheory
open scoped ContDiff

set_option autoImplicit false

namespace Langlands.Analysis.OperatorIdeals

open Langlands.Plancherel Langlands.HarmonicAnalysis.TorusFourier

section TorusSliceBounds

variable {J E : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "T" => J → Circle
local notation "A" => J → ℝ

omit [DecidableEq J] in
private theorem smooth_torusSlice {F : T → E → ℂ}
    (hF : ContDiff ℝ ∞ (fun p : A × E => F (finiteTorusExp p.1) p.2)) (x : E) :
    IsSmoothFiniteTorusFunction (fun z => F z x) := by
  unfold IsSmoothFiniteTorusFunction
  exact hF.comp (contDiff_id.prodMk contDiff_const)

private theorem contDiff_torusPartialDeriv_lift {F : T → E → ℂ}
    (hF : ContDiff ℝ ∞ (fun p : A × E => F (finiteTorusExp p.1) p.2)) (j : J) (k : ℕ) :
    ContDiff ℝ ∞ (fun p : A × E =>
      ((torusPartialDeriv j)^[k] (fun z => F z p.2)) (finiteTorusExp p.1)) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
      let G : A × E → ℂ := fun p => ((torusPartialDeriv j)^[k] (fun z => F z p.2)) (finiteTorusExp p.1)
      let v : A × E := (Pi.single j 1, 0)
      have hD : ContDiff ℝ ∞ (fun p => (fderiv ℝ G p) v) :=
        (ih.fderiv_right (by simp)).clm_apply contDiff_const
      have he : (fun p : A × E =>
          ((torusPartialDeriv j)^[k + 1] (fun z => F z p.2)) (finiteTorusExp p.1)) =
          fun p => (fderiv ℝ G p) v := by
        funext p
        rw [Function.iterate_succ_apply', torusPartialDeriv_finiteTorusExp
          (isSmoothFiniteTorusFunction_iterate_torusPartialDeriv (smooth_torusSlice hF p.2) j k)]
        let i := ContinuousLinearMap.inl ℝ A E
        have hi : HasFDerivAt (fun t : A => (t, p.2)) i p.1 := by
          simpa only [i, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add] using
            (i.hasFDerivAt (x := p.1)).add_const ((0 : A), p.2)
        have hDiff : DifferentiableAt ℝ G p := ih.differentiable (by simp) p
        have hd₀ : HasFDerivAt G (fderiv ℝ G p) (p.1, p.2) := hDiff.hasFDerivAt
        have hd := HasFDerivAt.comp p.1 hd₀ hi
        exact congrArg (fun D : A →L[ℝ] ℂ => D (Pi.single j 1)) hd.fderiv
      rw [he]
      exact hD

private theorem continuous_torusIteratedPartial {F : T → E → ℂ}
    (hF : ContDiff ℝ ∞ (fun p : A × E => F (finiteTorusExp p.1) p.2)) (j : J) (k : ℕ) :
    Continuous (fun q : T × E => ((torusPartialDeriv j)^[k] (fun z => F z q.2)) q.1) :=
  ((isOpenQuotientMap_finiteTorusExp J).prodMap IsOpenQuotientMap.id).isQuotientMap.continuous_iff.mpr
    (contDiff_torusPartialDeriv_lift hF j k).continuous

private theorem exists_uniform_torus_bounds {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (s : C(X, E)) (k : ℕ) {F : T → E → ℂ}
    (hF : ContDiff ℝ ∞ (fun p : A × E => F (finiteTorusExp p.1) p.2))
    (hC : Continuous (fun p : T × E => F p.1 p.2)) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ z x, ‖F z (s x)‖ ≤ M) ∧
      (∀ j z x, ‖((torusPartialDeriv j)^[k] (fun w => F w (s x))) z‖ ≤ M) := by
  let i : T × X → T × E := fun p => (p.1, s p.2)
  have hi : Continuous i := continuous_fst.prodMk (s.continuous.comp continuous_snd)
  obtain ⟨M₀, hM₀⟩ := isCompact_univ.exists_bound_of_continuousOn (hC.comp hi).continuousOn
  choose Mj hMj using fun j => isCompact_univ.exists_bound_of_continuousOn
    ((continuous_torusIteratedPartial hF j k).comp hi).continuousOn
  let M := |M₀| + ∑ j, |Mj j|
  have hs : 0 ≤ ∑ j, |Mj j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨M, add_nonneg (abs_nonneg _) hs, ?_, ?_⟩
  · intro z x
    exact (hM₀ (z, x) (Set.mem_univ _)).trans ((le_abs_self _).trans
      (le_add_of_nonneg_right hs))
  · intro j z x
    have hj : |Mj j| ≤ ∑ l, |Mj l| := Finset.single_le_sum (f := fun l => |Mj l|)
      (fun l _ => abs_nonneg _) (Finset.mem_univ j)
    exact (hMj j (z, x) (Set.mem_univ _)).trans ((le_abs_self _).trans
      (hj.trans (le_add_of_nonneg_left (abs_nonneg _))))

end TorusSliceBounds

/-- Lift a continuous real coordinate profile to a product of circles by
applying arccosine to each scaled coordinate. -/
def compactTorusSection {X J : Type*} [TopologicalSpace X]
    (h : C(X, J → ℝ)) (r : ℝ) : C(X, J → Circle) :=
  ⟨fun a j => Circle.exp (Real.arccos (h a j / r)),
    continuous_pi fun j => Circle.exp.continuous.comp
      (Real.continuous_arccos.comp (((continuous_apply j).comp h.continuous).div_const r))⟩

section SmoothExtension

variable {X E E' : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  (μ : Measure X) [IsFiniteMeasure μ]

private def torusHaar (J : Type*) [Fintype J] : Measure (J → Circle) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

private instance (J : Type*) [Fintype J] : (torusHaar J).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

private instance (J : Type*) [Fintype J] : IsProbabilityMeasure (torusHaar J) :=
  ⟨Measure.haarMeasure_self⟩

set_option maxHeartbeats 1600000 in
/-- A continuous kernel with a smooth extension along finite-dimensional real output
coordinates and real input coordinates gives a trace-class endomorphism of `L²`. -/
theorem isTraceClass_continuousKernelOperator_of_smooth_extension
    (P : C(X × X, ℂ)) (x : C(X, E)) (y : C(X, E'))
    (F : E × E' → ℂ) (hF : ContDiff ℝ ∞ F) (hP : ∀ a b, P (a, b) = F (x a, y b)) :
    IsTraceClass ((ContinuousMap.toLp 2 μ ℂ).comp (continuousKernelProfile μ P)) := by
  let J := Fin (Module.finrank ℝ E)
  let U : E ≃L[ℝ] (J → ℝ) := (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  let h : C(X, J → ℝ) := ⟨fun a => U (x a), U.continuous.comp x.continuous⟩
  let r : ℝ := ‖h‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let p := compactTorusSection h r
  let v : (J → Circle) → J → ℝ := fun z j => r * ((z j : Circle) : ℂ).re
  have hv : Continuous v := continuous_pi fun j =>
    continuous_const.mul (Complex.continuous_re.comp (continuous_subtype_val.comp (continuous_apply j)))
  have hvp (a : X) : v (p a) = h a := by
    funext j
    have hnorm : ‖h a j‖ ≤ r := (norm_le_pi_norm (h a) j).trans
      ((h.norm_coe_le_norm a).trans (le_add_of_nonneg_right zero_le_one))
    have hdiv : |h a j / r| ≤ 1 := by
      rw [abs_div, abs_of_pos hr, div_le_one hr, ← Real.norm_eq_abs]
      exact hnorm
    have h1 : -1 ≤ h a j / r := (abs_le.mp hdiv).1
    have h2 : h a j / r ≤ 1 := (abs_le.mp hdiv).2
    change r * ((Circle.exp (Real.arccos (h a j / r)) : Circle) : ℂ).re = h a j
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Real.cos_arccos h1 h2]
    field_simp
  have hvExp : ContDiff ℝ ∞ (fun t : J → ℝ => v (finiteTorusExp t)) := by
    apply contDiff_pi.mpr
    intro j
    change ContDiff ℝ ∞ (fun t : J → ℝ => r * ((Circle.exp (t j) : Circle) : ℂ).re)
    simp_rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
    exact contDiff_const.mul (Real.contDiff_cos.comp (contDiff_apply ℝ (fun _ ↦ ℝ) j))
  let G : (J → Circle) → E' → ℂ := fun z b => F (U.symm (v z), b)
  have hG : ContDiff ℝ ∞ (fun q : (J → ℝ) × E' => G (finiteTorusExp q.1) q.2) :=
    hF.comp ((U.symm.toContinuousLinearMap.contDiff.comp (hvExp.comp contDiff_fst)).prodMk contDiff_snd)
  have hcG : Continuous (fun q : (J → Circle) × E' => G q.1 q.2) :=
    hF.continuous.comp ((U.symm.continuous.comp (hv.comp continuous_fst)).prodMk continuous_snd)
  let Q : C((J → Circle) × X, ℂ) :=
    ⟨fun q => G q.1 (y q.2), hcG.comp (continuous_fst.prodMk (y.continuous.comp continuous_snd))⟩
  obtain ⟨M, hM, hval, hder⟩ := exists_uniform_torus_bounds y (4 * Fintype.card J) hG hcG
  obtain ⟨A, B, hAB⟩ := exists_torus_kernel_factorization (torusHaar J) Q p hM
    (fun a => smooth_torusSlice hG (y a)) hval hder
  refine isTraceClass_continuousKernelOperator_of_factorization μ (torusHaar J) P A B (fun a b => ?_)
  rw [hAB, hP]
  change F (x a, y b) = F (U.symm (v (p a)), y b)
  rw [hvp]
  exact congrArg (fun u => F (u, y b)) (U.symm_apply_apply (x a)).symm

end SmoothExtension
end Langlands.Analysis.OperatorIdeals
