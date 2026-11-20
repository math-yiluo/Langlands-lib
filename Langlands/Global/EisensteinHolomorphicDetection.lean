import Langlands.Analysis.HolomorphicTaylor
import Langlands.Global.EisensteinEvaluationMatrix
import Langlands.Global.EisensteinJetDetection
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # One-parameter holomorphic detection of specialization -/

noncomputable section

open Matrix Module

namespace Langlands.Global.EisensteinJet

open Langlands.Analysis (holomorphicAtSubring holomorphicTaylor holomorphicTaylor_ne_zero
  coeff_holomorphicTaylor constantCoeff_holomorphicTaylor)

variable {V X : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

local notation "I" => Fin (finrank ℂ V)

/-- The evaluation matrix with its entries bundled as functions holomorphic
at the point of specialization. -/
def holomorphicEvaluationMatrix (z : ℂ) (E : ℂ → (V →ₗ[ℂ] (X → ℂ)))
    (hE : ∀ v x, AnalyticAt ℂ (fun t => E t v x) z)
    (p : I → X) (e : V ≃ₗ[ℂ] (I → ℂ)) :
    Matrix I I (holomorphicAtSubring z) :=
  Matrix.of fun i j => ⟨fun t => evaluationMatrix p e (E t) i j,
    hE (e.symm (Pi.single j 1)) (p i)⟩

omit [FiniteDimensional ℂ V] in
private theorem evaluationMatrix_mulVec (p : I → X) (e : V ≃ₗ[ℂ] (I → ℂ))
    (f : V →ₗ[ℂ] (X → ℂ)) (v : V) :
    evaluationMatrix p e f *ᵥ e v = fun i => f v (p i) := by
  let b := (Pi.basisFun ℂ I).map e.symm
  let L := (LinearMap.funLeft ℂ ℂ p).comp f
  have hmatrix : LinearMap.toMatrix b (Pi.basisFun ℂ I) L = evaluationMatrix p e f := by
    ext i j
    simp [b, L, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, evaluationMatrix]
  have hb : ⇑(b.repr v) = e v := by
    funext i
    simp [b, Pi.basisFun_repr]
  have hmul := LinearMap.toMatrix_mulVec_repr b (Pi.basisFun ℂ I) L v
  rw [hmatrix, hb] at hmul
  funext i
  simpa only [L, Pi.basisFun_repr, LinearMap.comp_apply, LinearMap.funLeft_apply] using
    congrFun hmul i

/-- In a one-parameter holomorphic family of maps from a finite-dimensional
space to functions, one injective member on the preconnected parameter set
gives a uniform finite derivative test for zero specialization. -/
theorem exists_derivativeDetectionOrder (U : Set ℂ) (hU : IsPreconnected U)
    (z t₁ : ℂ) (hz : z ∈ U) (ht₁ : t₁ ∈ U)
    (E : ℂ → (V →ₗ[ℂ] (X → ℂ)))
    (hE : ∀ v x, AnalyticOnNhd ℂ (fun t => E t v x) U)
    (hinj : Function.Injective (E t₁)) :
    ∃ d : ℕ, ∀ s : ℂ → V,
      (∀ ℓ : Dual ℂ V, AnalyticAt ℂ (fun t => ℓ (s t)) z) →
      (∀ x (k : Fin d), iteratedDeriv (k : ℕ) (fun t => E t (s t) x) z = 0) →
      s z = 0 := by
  obtain ⟨p, e, he⟩ := exists_evaluationMatrix_eq_one (E t₁) hinj
  let A := holomorphicEvaluationMatrix z E (fun v x => hE v x z hz) p e
  let eval (t : ℂ) : holomorphicAtSubring z →+* ℂ :=
    (Pi.evalRingHom (fun _ : ℂ => ℂ) t).comp (holomorphicAtSubring z).subtype
  have heval (t : ℂ) : (eval t).mapMatrix A = evaluationMatrix p e (E t) := rfl
  have hdet (t : ℂ) : A.det.val t = (evaluationMatrix p e (E t)).det :=
    ((eval t).map_det A).trans (congrArg Matrix.det (heval t))
  have hhol : AnalyticOnNhd ℂ A.det.val U := by
    rw [show A.det.val = fun t => (evaluationMatrix p e (E t)).det from funext hdet]
    intro t ht
    simp_rw [Matrix.det_apply']
    apply Finset.analyticAt_fun_sum
    intro σ _
    refine analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => ?_)
    exact hE (e.symm (Pi.single i 1)) (p (σ i)) t ht
  have hat : analyticOrderAt A.det.val t₁ = 0 :=
    (hhol t₁ ht₁).analyticOrderAt_eq_zero.mpr (by rw [hdet, he, Matrix.det_one]; exact one_ne_zero)
  have horder := hhol.analyticOrderAt_ne_top_of_isPreconnected hU ht₁ hz
    (hat ▸ ENat.zero_ne_top)
  let B := (holomorphicTaylor z).mapMatrix A
  have hB : B.det ≠ 0 :=
    ((holomorphicTaylor z).map_det A) ▸ holomorphicTaylor_ne_zero z A.det horder
  refine ⟨coefficientCount B, fun s hs hzero => ?_⟩
  let x (i : I) : holomorphicAtSubring z :=
    ⟨fun t => e (s t) i, hs ((LinearMap.proj i).comp e.toLinearMap)⟩
  let y := holomorphicTaylor z ∘ x
  have hval (i : I) : ((A *ᵥ x) i).val = fun t => E t (s t) (p i) := by
    funext t
    have hv := RingHom.map_mulVec (eval t) A x i
    rw [show A.map (eval t) = evaluationMatrix p e (E t) from heval t] at hv
    exact hv.trans (congrFun (evaluationMatrix_mulVec p e (E t) (s t)) i)
  have hobs : ∀ i (k : Fin (coefficientCount B)), PowerSeries.coeff (k : ℕ) ((B *ᵥ y) i) = 0 := by
    intro i k
    rw [← show holomorphicTaylor z ((A *ᵥ x) i) = (B *ᵥ y) i from
      RingHom.map_mulVec (holomorphicTaylor z) A x i,
      coeff_holomorphicTaylor, hval, hzero (p i) k, zero_div]
  apply e.injective
  funext i
  simpa only [B, y, Function.comp_apply, constantCoeff_holomorphicTaylor, x, e.map_zero,
    Pi.zero_apply] using constantCoeff_eq_zero_of_mulVec B hB y hobs i

/-- For several parameters, test along the complex line joining the base point
to one injective point in its holomorphy ball. -/
theorem exists_lineDerivativeDetectionOrder {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] (z t₁ : W) (R : ℝ) (ht₁ : t₁ ∈ Metric.ball z R)
    (E : W → (V →ₗ[ℂ] (X → ℂ)))
    (hE : ∀ v x, AnalyticOnNhd ℂ (fun t => E t v x) (Metric.ball z R))
    (hinj : Function.Injective (E t₁)) :
    ∃ d : ℕ, ∀ s : W → V,
      (∀ ℓ : Dual ℂ V, AnalyticAt ℂ (fun t => ℓ (s t)) z) →
      (∀ x (k : Fin d), iteratedDeriv (k : ℕ) (fun t : ℂ =>
        E (AffineMap.lineMap z t₁ t) (s (AffineMap.lineMap z t₁ t)) x) 0 = 0) →
      s z = 0 := by
  classical
  let line := AffineMap.lineMap (k := ℂ) z t₁
  have hz₁ : ‖t₁ - z‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using ht₁
  have hR : 0 < R := (norm_nonneg _).trans_lt hz₁
  let r : ℝ := if t₁ = z then 2 else R / ‖t₁ - z‖
  have hr : 1 < r := by
    by_cases h : t₁ = z
    · simp [r, h]
    · simp only [r, ite_eq_right h, lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr h)), one_mul]
      exact hz₁
  have hline (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) r) : line t ∈ Metric.ball z R := by
    change AffineMap.lineMap z t₁ t ∈ Metric.ball z R
    rw [Metric.mem_ball, dist_eq_norm, AffineMap.lineMap_apply_module',
      add_sub_cancel_right, norm_smul]
    by_cases h : t₁ = z
    · simpa [h] using hR
    · have ht' : ‖t‖ < R / ‖t₁ - z‖ := by simpa [r, h, Metric.mem_ball, dist_zero_right] using ht
      exact (lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr h))).mp ht'
  have ha (t : ℂ) : AnalyticAt ℂ (fun u : ℂ => line u) t := by
    change AnalyticAt ℂ (fun u : ℂ => AffineMap.lineMap z t₁ u) t
    simp_rw [AffineMap.lineMap_apply_module']
    exact (analyticAt_id.smul analyticAt_const).add analyticAt_const
  have hzero : (0 : ℂ) ∈ Metric.ball 0 r := Metric.mem_ball_self (zero_lt_one.trans hr)
  have hone : (1 : ℂ) ∈ Metric.ball 0 r := by simpa [Metric.mem_ball, dist_zero_right] using hr
  obtain ⟨d, hd⟩ := exists_derivativeDetectionOrder (Metric.ball (0 : ℂ) r)
    (convex_ball (0 : ℂ) r).isPreconnected 0 1 hzero hone (fun t => E (line t))
    (fun v x t ht => (hE v x _ (hline t ht)).comp (ha t))
    (by simpa [line] using hinj)
  refine ⟨d, fun s hs hvanish => ?_⟩
  have hcomp (ℓ : Dual ℂ V) : AnalyticAt ℂ (fun t : ℂ => ℓ (s (line t))) 0 :=
    (show AnalyticAt ℂ (fun u => ℓ (s u)) (line 0) from by simpa [line] using hs ℓ).comp (ha 0)
  simpa [line] using hd (fun t => s (line t)) hcomp hvanish

end Langlands.Global.EisensteinJet
