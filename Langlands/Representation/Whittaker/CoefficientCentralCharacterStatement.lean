import Langlands.Representation.Whittaker.Algebraic
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.Group.Basic

namespace Langlands.Whittaker

universe uG uV

/-- A one-dimensional equivariant-functional space gives one locally constant
central character on all of its coefficient images. -/
def CoefficientCentralCharacterStatement (G : Type uG) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∀ (N : Subgroup G) (θ : N →* ℂˣ),
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ ρ : Representation ℂ G V,
    IsSmooth ρ → Nonempty ((functionals N θ ρ) ≃ₗ[ℂ] ℂ) →
    ∃! χ : Subgroup.center G →* ℂˣ,
      IsLocallyConstant (χ : Subgroup.center G → ℂˣ) ∧
      ∀ (ℓ : functionals N θ ρ) (f : (coefficientModel ρ ℓ).toSubmodule)
        (z : Subgroup.center G) (g : G),
        f.val.val ((z : G) * g) = (χ z : ℂ) * f.val.val g

end Langlands.Whittaker
