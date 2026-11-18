import Langlands.Representation.Archimedean.SmoothHilbert
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Differentiating the real exponential in the smooth-vector topology -/

noncomputable section

open scoped Manifold ContDiff Topology Matrix.Norms.Operator
open Filter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

universe uH

variable (F : Type) [RCLike F] (n : ℕ)

local notation "GL" => Langlands.GeneralLinear n F
local notation "Mat" => Matrix (Fin n) (Fin n) F
local notation "I" => matrixModel F n

@[simp]
theorem generalLinearRealExp_zero (X : Mat) : generalLinearRealExp F n X 0 = 1 := by
  apply Units.ext
  simp

/-- The exponential curve is smooth for the real matrix manifold structure. -/
theorem contMDiff_generalLinearRealExp (X : Mat) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (generalLinearRealExp F n X) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  rw [contMDiff_iff_contDiff]
  have h : AnalyticOnNhd ℝ (NormedSpace.exp : Mat → Mat) Set.univ := fun A _ =>
    NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) A
      (by rw [NormedSpace.expSeries_radius_eq_top, Metric.mem_eball]; exact edist_lt_top _ _)
  exact h.contDiff.comp (contDiff_id.smul contDiff_const)

/-- The tangent vector of the actual exponential at zero is the input matrix. -/
theorem hasMFDerivAt_generalLinearRealExp (X : Mat) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (generalLinearRealExp F n X) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight X) := by
  refine ⟨(contMDiff_generalLinearRealExp F n X).continuous.continuousAt, ?_⟩
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)).hasFDerivAt
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  simp only [writtenInExtChartAt, extChartAt, mfld_simps]
  convert h.hasFDerivWithinAt using 1
  · rfl
  · ext
    rfl

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (R : Langlands.GeneralLinear n F →* (H →L[ℂ] H))

private theorem hasDerivAt_exponentialOrbit (X : Mat) (v : smoothVectors I R) (g : GL) :
    HasDerivAt (fun t : ℝ => R (g * generalLinearRealExp F n X t) v)
      (R g (smoothLieDerivative I R X v : H)) 0 := by
  have hd : MDifferentiableAt I 𝓘(ℝ, H) (fun h : GL => R (g * h) v) 1 :=
    (v.property.comp (contMDiff_const.mul contMDiff_id)).mdifferentiableAt (by simp)
  have hf : HasMFDerivAt I 𝓘(ℝ, H) (fun h : GL => R (g * h) v) (generalLinearRealExp F n X 0)
      (mfderiv I 𝓘(ℝ, H) (fun h : GL => R (g * h) v) 1) := by
    rw [generalLinearRealExp_zero]
    exact hd.hasMFDerivAt
  have h := HasMFDerivAt.comp (f := generalLinearRealExp F n X) 0 hf
    (hasMFDerivAt_generalLinearRealExp F n X)
  rw [hasMFDerivAt_iff_hasFDerivAt] at h
  have hv : ((mfderiv I 𝓘(ℝ, H) (fun h : GL => R (g * h) v) 1).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight X)) (1 : ℝ) =
      R g (smoothLieDerivative I R X v : H) := by
    rw [smoothLieDerivative_apply, apply_lieDerivative I R g X v.property]
    simp
  exact h.hasDerivAt.congr_deriv hv

private theorem hasDerivAt_mixedPartial {f : ℝ × ℝ → H} (hf : ContDiff ℝ ∞ f) {a : H}
    (ha : HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => f (t, s)) 0) a 0) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => f (t, s)) 0) a 0 := by
  let e₁ : ℝ × ℝ := (1, 0)
  let e₂ : ℝ × ℝ := (0, 1)
  have h₁ (s : ℝ) : deriv (fun t : ℝ => f (t, s)) 0 = fderiv ℝ f (0, s) e₁ :=
    ((hf.differentiable (by simp) (0, s)).hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 s))).deriv
  have h₂ (t : ℝ) : deriv (fun s : ℝ => f (t, s)) 0 = fderiv ℝ f (t, 0) e₂ :=
    ((hf.differentiable (by simp) (t, 0)).hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const 0 t).prodMk (hasDerivAt_id 0))).deriv
  have hd : DifferentiableAt ℝ (fderiv ℝ f) ((0, 0) : ℝ × ℝ) :=
    (hf.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero _
  have h₂₁ : HasDerivAt (fun s : ℝ => fderiv ℝ f (0, s) e₁)
      (fderiv ℝ (fderiv ℝ f) (0, 0) e₂ e₁) 0 := by
    simpa only [Function.comp_apply, e₁, e₂, map_zero, add_zero] using
      (hd.hasFDerivAt.comp_hasDerivAt 0
        ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ)))).clm_apply
          (hasDerivAt_const 0 e₁)
  have h₁₂ : HasDerivAt (fun t : ℝ => fderiv ℝ f (t, 0) e₂)
      (fderiv ℝ (fderiv ℝ f) (0, 0) e₁ e₂) 0 := by
    simpa only [Function.comp_apply, e₁, e₂, map_zero, add_zero] using
      (hd.hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => (t, 0)) 0
        ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ)))).clm_apply
          (hasDerivAt_const 0 e₂)
  have hsymm : IsSymmSndFDerivAt ℝ f (0, 0) :=
    hf.contDiffAt.isSymmSndFDerivAt (by simp)
  simp_rw [h₁] at ha
  simp_rw [h₂]
  exact h₁₂.congr_deriv ((hsymm e₁ e₂).trans (h₂₁.unique ha))

private theorem smoothIteratedExponentialOrbit (X : Mat) (v : smoothVectors I R)
    (word : List Mat) :
    let u := fun t : ℝ => smoothRepresentation I R (generalLinearRealExp F n X t) v
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, H) ∞
      (fun p : ℝ × GL => R p.2 (smoothIteratedLieDerivative I R word (u p.1) : H)) ∧
    ∀ g : GL, HasDerivAt (fun t : ℝ => R g (smoothIteratedLieDerivative I R word (u t) : H))
      (R g (smoothIteratedLieDerivative I R word (smoothLieDerivative I R X v) : H)) 0 := by
  let u := fun t : ℝ => smoothRepresentation I R (generalLinearRealExp F n X t) v
  change ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, H) ∞
      (fun p : ℝ × GL => R p.2 (smoothIteratedLieDerivative I R word (u p.1) : H)) ∧
    ∀ g : GL, HasDerivAt (fun t : ℝ => R g (smoothIteratedLieDerivative I R word (u t) : H))
      (R g (smoothIteratedLieDerivative I R word (smoothLieDerivative I R X v) : H)) 0
  induction word with
  | nil =>
      refine ⟨?_, fun g => ?_⟩
      · have hmul : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
            (fun p : ℝ × GL => p.2 * generalLinearRealExp F n X p.1) :=
          contMDiff_snd.mul ((contMDiff_generalLinearRealExp F n X).comp contMDiff_fst)
        simpa only [Function.comp_def, orbitMap, u, smoothIteratedLieDerivative,
          LinearMap.id_apply, smoothRepresentation_apply, map_mul, mul_apply_eq_comp]
          using v.property.comp hmul
      · simpa only [u, smoothIteratedLieDerivative, LinearMap.id_apply,
          smoothRepresentation_apply, map_mul, mul_apply_eq_comp]
          using hasDerivAt_exponentialOrbit F n R X v g
  | cons Y word ih =>
      let f := fun (p : ℝ × GL) (s : ℝ) =>
        R (p.2 * generalLinearRealExp F n Y s) (smoothIteratedLieDerivative I R word (u p.1) : H)
      have hf : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, H) ∞
          (Function.uncurry f) := by
        have h : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
            (fun q : (ℝ × GL) × ℝ => (q.1.1, q.1.2 * generalLinearRealExp F n Y q.2)) :=
          contMDiff_fst.fst.prodMk
            (contMDiff_fst.snd.mul ((contMDiff_generalLinearRealExp F n Y).comp contMDiff_snd))
        exact ih.1.comp h
      have hs (p : ℝ × GL) : HasDerivAt (f p)
          (R p.2 (smoothIteratedLieDerivative I R (Y :: word) (u p.1) : H)) 0 :=
        hasDerivAt_exponentialOrbit F n R Y (smoothIteratedLieDerivative I R word (u p.1)) p.2
      refine ⟨?_, fun g => ?_⟩
      · intro p
        have hd := (hf.contMDiffAt (x := (p, 0))).mfderiv_apply (m := ∞)
          (x₀ := p) f (fun _ => (0 : ℝ)) id (fun _ => (1 : ℝ))
          contMDiffAt_const contMDiffAt_id contMDiffAt_const (by simp)
        have he (q : ℝ × GL) : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, H) (f q) 0 (1 : ℝ) =
            R q.2 (smoothIteratedLieDerivative I R (Y :: word) (u q.1) : H) := by
          have hmf : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, H) (f q) 0 : ℝ →L[ℝ] H) =
              fderiv ℝ (f q) 0 := mfderiv_eq_fderiv
          exact (congrArg (fun A : ℝ →L[ℝ] H => A (1 : ℝ)) hmf).trans (hs q).deriv
        have hd' : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, H) ∞
            (fun q : ℝ × GL => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, H) (f q) 0 (1 : ℝ)) p := by
          simpa only [inTangentCoordinates_model_space, id_eq] using! hd
        rwa [funext he] at hd'
      · have hpair : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
            ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) ∞ (fun q : ℝ × ℝ => ((q.1, g), q.2)) :=
          (contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd
        have hfg := hf.comp hpair
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, contMDiff_iff_contDiff] at hfg
        have ht (s : ℝ) : deriv (fun t : ℝ => f (t, g) s) 0 =
            R (g * generalLinearRealExp F n Y s)
              (smoothIteratedLieDerivative I R word (smoothLieDerivative I R X v) : H) :=
          (ih.2 (g * generalLinearRealExp F n Y s)).deriv
        have hst : HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => f (t, g) s) 0)
            (R g (smoothIteratedLieDerivative I R (Y :: word) (smoothLieDerivative I R X v) : H)) 0 := by
          simp_rw [ht]
          exact hasDerivAt_exponentialOrbit F n R Y
            (smoothIteratedLieDerivative I R word (smoothLieDerivative I R X v)) g
        have hts := hasDerivAt_mixedPartial
          (f := fun q : ℝ × ℝ => f (q.1, g) q.2) hfg hst
        have he (t : ℝ) : deriv (f (t, g)) 0 =
            R g (smoothIteratedLieDerivative I R (Y :: word) (u t) : H) := (hs (t, g)).deriv
        simpa only [he] using hts

/-- The difference quotient of the exponential orbit, as a genuine smooth vector. -/
def smoothHilbertExponentialSlope (X : Mat) (y : DerivativeSmoothVectors I R) (t : ℝ) :
    DerivativeSmoothVectors I R :=
  t⁻¹ • (DerivativeSmoothVectors.representation I R (generalLinearRealExp F n X t) y - y)

/-- The exponential difference quotients converge in every word seminorm at once. -/
theorem tendsto_smoothHilbertExponentialSlope (X : Mat) (y : DerivativeSmoothVectors I R) :
    Tendsto (smoothHilbertExponentialSlope F n R X y) (𝓝[≠] 0)
      (𝓝 (DerivativeSmoothVectors.operator I R X y)) := by
  apply (DerivativeSmoothVectors.isEmbedding_derivativeCoordinates I R).tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro word
  have h := (smoothIteratedExponentialOrbit F n R X (DerivativeSmoothVectors.toSmooth I R y) word).2 1
  change Tendsto (fun t => DerivativeSmoothVectors.derivativeCoordinates I R
      (smoothHilbertExponentialSlope F n R X y t) word) (𝓝[≠] 0)
    (𝓝 (DerivativeSmoothVectors.derivativeCoordinates I R
      (DerivativeSmoothVectors.operator I R X y) word))
  simp only [smoothHilbertExponentialSlope, map_sub, LinearMap.map_smul_of_tower,
    Pi.smul_apply, Pi.sub_apply]
  simp only [DerivativeSmoothVectors.derivativeCoordinates_apply,
    DerivativeSmoothVectors.toSmooth_representation, DerivativeSmoothVectors.toSmooth_operator,
    ← smoothIteratedLieDerivative_apply]
  simpa only [zero_add, map_one, one_apply_eq_self, generalLinearRealExp_zero,
    Module.End.one_apply] using h.tendsto_slope_zero

/-- Every continuous functional on the derivative topology differentiates the
exponential orbit by applying the functional to the genuine Lie derivative. -/
theorem hasSmoothHilbertExponentialDerivatives :
    HasSmoothHilbertExponentialDerivatives F n R := by
  intro X y L
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  let L' := L.restrictScalars ℝ
  have h := (L'.continuous.tendsto _).comp (tendsto_smoothHilbertExponentialSlope F n R X y)
  simp only [Function.comp_def, smoothHilbertExponentialSlope, map_smul, map_sub] at h
  simpa only [zero_add, generalLinearRealExp_zero, map_one, Module.End.one_apply] using! h

end Langlands.Archimedean
