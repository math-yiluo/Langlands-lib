import Langlands.AlgebraicGeometry.Modules.PresheafPullbackTensor

universe u

open CategoryTheory

namespace Langlands.Scheme.Modules

/-- The canonical presheaf pullback tensor comparison is invertible for every scheme morphism. -/
def presheafPullbackTensorComparisonIsIsoStatement : Prop :=
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
    IsIso (presheafPullbackTensorComparison f)

end Langlands.Scheme.Modules
