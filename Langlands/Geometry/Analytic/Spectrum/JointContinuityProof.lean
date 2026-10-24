import Langlands.Geometry.Analytic.Spectrum.JointContinuityStatement

/-! # Proof of joint continuity for bounded multiplicative spectra -/

universe u v w

open Filter Topology

namespace Langlands.Analytic.BanachSpectrum

section Evaluation

variable {A : Type u} [NormedCommRing A]

/-- Evaluation at a spectrum point is `1`-Lipschitz for the norm. -/
theorem abs_sub_le_norm_sub (x : BanachSpectrum A) (a b : A) :
    |x a - x b| ≤ ‖a - b‖ :=
  (abs_sub_map_le_sub x.toMulRingSeminorm a b).trans (x.le_norm (a - b))

/-- Evaluation is jointly continuous in the spectrum point and the algebra element. -/
theorem continuous_eval : Continuous (fun p : BanachSpectrum A × A => p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, a₀⟩
  have h₁ : Tendsto (fun p : BanachSpectrum A × A => p.1 a₀) (𝓝 (x₀, a₀)) (𝓝 (x₀ a₀)) :=
    ((evaluation a₀).continuous.comp continuous_fst).tendsto (x₀, a₀)
  have h₂ : Tendsto (fun p : BanachSpectrum A × A => ‖a₀ - p.2‖) (𝓝 (x₀, a₀)) (𝓝 0) := by
    have h := ((continuous_const.sub continuous_snd).norm.tendsto (x₀, a₀) :
      Tendsto (fun p : BanachSpectrum A × A => ‖a₀ - p.2‖) (𝓝 (x₀, a₀)) (𝓝 ‖a₀ - a₀‖))
    simpa using h
  refine h₁.congr_dist (squeeze_zero (fun _ => dist_nonneg) (fun p => ?_) h₂)
  rw [Real.dist_eq]
  exact abs_sub_le_norm_sub p.1 a₀ p.2

/-- Evaluating a continuous family of spectrum points at a continuous family of
algebra elements is continuous. -/
theorem _root_.Continuous.banachSpectrum_apply {X : Type w} [TopologicalSpace X]
    {x : X → BanachSpectrum A} {a : X → A} (hx : Continuous x) (ha : Continuous a) :
    Continuous (fun t => x t (a t)) :=
  continuous_eval.comp (hx.prodMk ha)

end Evaluation

/-- A family of bounded ring maps continuous on each algebra element has jointly
continuous pullback on spectra. -/
theorem continuous_comap_of_continuous_apply {A : Type u} [NormedCommRing A]
    {B : Type v} [NormedCommRing B] {T : Type w} [TopologicalSpace T]
    (f : T → BoundedRingHom A B) (hf : ∀ a : A, Continuous (fun t : T => f t a)) :
    Continuous (fun p : T × BanachSpectrum B => comap (f p.1) p.2) :=
  continuous_induced_rng.mpr <| continuous_pi fun a =>
    continuous_snd.banachSpectrum_apply ((hf a).comp continuous_fst)

theorem uniformEvaluationBound : UniformEvaluationBoundStatement.{u} :=
  fun _ _ x a b => abs_sub_le_norm_sub x a b

theorem jointEvaluationContinuity : JointEvaluationContinuityStatement.{u} :=
  fun _ _ => continuous_eval

theorem parametricPullbackContinuity : ParametricPullbackContinuityStatement.{u, v, w} :=
  fun _ _ _ _ _ _ f hf => continuous_comap_of_continuous_apply f hf

theorem jointContinuity : JointContinuityStatement.{u, v, w} :=
  ⟨uniformEvaluationBound, jointEvaluationContinuity, parametricPullbackContinuity⟩

end Langlands.Analytic.BanachSpectrum
