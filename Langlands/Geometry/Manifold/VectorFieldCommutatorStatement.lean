import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! # The scalar differential commutator for actual manifold vector fields -/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- Applying the derivative to the actual vector-field bracket equals the
commutator of the two directional derivatives. -/
def smoothVectorFieldCommutator [CompleteSpace E] [I.Boundaryless] : Prop :=
  ∀ (V W : (x : M) → TangentSpace I x),
    MDifferentiable I I.tangent (fun x => (V x : TangentBundle I M)) →
    MDifferentiable I I.tangent (fun x => (W x : TangentBundle I M)) →
    ∀ (f : M → ℂ), ContMDiff I 𝓘(ℝ, ℂ) ∞ f →
    ∀ x : M,
      mvfderiv I f x (VectorField.mlieBracket I V W x) =
        mvfderiv I (fun y => mvfderiv I f y (W y)) x (V x) -
          mvfderiv I (fun y => mvfderiv I f y (V y)) x (W x)

end Langlands.Geometry.Manifold
