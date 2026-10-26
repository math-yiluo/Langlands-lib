import Langlands.Representation.Whittaker.GeneralizedCoefficient
import Mathlib.RepresentationTheory.Irreducible

/-!
# A generalized-coefficient kernel criterion for scalar uniqueness

This internal conditional statement uses actual generalized coefficients and
distribution pushforward. Its proof is a separate obligation.
-/

namespace Langlands.Whittaker

open MeasureTheory MeasureTheory.Measure

universe uG uV

/-- A fixed nonzero algebraic functional on the smooth dual, together with
invariance of all the corresponding generalized coefficients under a
measure-preserving involutive anti-automorphism, forces scalar uniqueness
in the given subspace of the full algebraic dual. -/
def GeneralizedCoefficientKernelStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsHaarMeasure μ] [IsMulRightInvariant μ] [IsInvInvariant μ]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hAdmissible : IsAdmissible ρ),
    ρ.IsIrreducible →
    ∀ (τ : G ≃ₜ G),
      Function.Involutive τ →
      (∀ g h : G, τ (g * h) = τ h * τ g) →
      MeasurePreserving τ μ μ →
      ∀ (W : Submodule ℂ (Module.Dual ℂ V))
        (η : Module.Dual ℂ (SmoothDual ρ)),
        η ≠ 0 →
        (∀ ℓ : W,
          HarmonicAnalysis.Distribution.pushforward τ
              (generalizedCoefficient μ ρ hAdmissible.1 ℓ.val η) =
            generalizedCoefficient μ ρ hAdmissible.1 ℓ.val η) →
        ∀ ℓ₁ ℓ₂ : W, ℓ₁.val ≠ 0 →
          ∃! c : ℂ, ℓ₂ = c • ℓ₁

end Langlands.Whittaker
