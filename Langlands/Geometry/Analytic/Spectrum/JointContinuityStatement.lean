import Langlands.Geometry.Analytic.Spectrum.Definitions

/-! # Joint continuity targets for bounded multiplicative spectra -/

universe u v w

namespace Langlands.Analytic.BanachSpectrum

/-- Evaluation has a norm Lipschitz bound independent of the spectrum point. -/
def UniformEvaluationBoundStatement : Prop :=
  ∀ (A : Type u) [NormedCommRing A] (x : BanachSpectrum A) (a b : A),
    |x a - x b| ≤ ‖a - b‖

/-- Evaluation is continuous when both the spectrum point and the algebra
element vary, with the pointwise spectrum topology and the norm topology. -/
def JointEvaluationContinuityStatement : Prop :=
  ∀ (A : Type u) [NormedCommRing A],
    Continuous (fun p : BanachSpectrum A × A => p.1 p.2)

/-- A family of bounded ring maps continuous on each algebra element induces
a jointly continuous family of pullbacks on the concrete spectra. -/
def ParametricPullbackContinuityStatement : Prop :=
  ∀ (A : Type u) [NormedCommRing A] (B : Type v) [NormedCommRing B]
    (T : Type w) [TopologicalSpace T] (f : T → BoundedRingHom A B),
    (∀ a : A, Continuous (fun t : T => f t a)) →
      Continuous (fun p : T × BanachSpectrum B => comap (f p.1) p.2)

/-- The uniform estimate, joint evaluation and parametric pullback targets. -/
def JointContinuityStatement : Prop :=
  UniformEvaluationBoundStatement.{u} ∧
    JointEvaluationContinuityStatement.{u} ∧
      ParametricPullbackContinuityStatement.{u, v, w}

end Langlands.Analytic.BanachSpectrum
