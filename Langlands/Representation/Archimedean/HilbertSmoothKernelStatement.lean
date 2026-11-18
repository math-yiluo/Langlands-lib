import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Smoothness of Hilbert-valued maps from their scalar kernels

The finite-dimensional real-manifold specialization of K.-H. Neeb,
*On Differentiable Vectors for Representations of Infinite Dimensional Lie
Groups* (arXiv:1002.1602v3), Theorem 7.1: a map from a manifold to a Hilbert
space is smooth if and only if its scalar kernel is smooth. This module states
the criterion only; it proves nothing.
-/

noncomputable section
set_option autoImplicit false
universe uA uM uH
open scoped Manifold ContDiff

namespace Langlands.Archimedean

/-- Neeb's Hilbert smooth-kernel criterion (Theorem 7.1) for manifolds without
boundary modelled on a finite-dimensional real normed space `A`: a map
`f : M → H` into a complex Hilbert space is real `C^∞` if and only if the
complex scalar kernel `(x, y) ↦ ⟪f x, f y⟫_ℂ` is real `C^∞` on `M × M`. -/
def HilbertSmoothKernelStatement : Prop :=
  ∀ (A : Type uA) [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    (M : Type uM) [TopologicalSpace M] [ChartedSpace A M] [IsManifold 𝓘(ℝ, A) ∞ M]
    (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : M → H),
    ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, H) ∞ f ↔
      ContMDiff (𝓘(ℝ, A).prod 𝓘(ℝ, A)) 𝓘(ℝ, ℂ) ∞
        (fun p : M × M => Inner.inner ℂ (f p.1) (f p.2))

end Langlands.Archimedean
