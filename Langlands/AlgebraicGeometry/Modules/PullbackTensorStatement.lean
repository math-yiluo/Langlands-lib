import Langlands.AlgebraicGeometry.Modules.PullbackTensor

universe u

open CategoryTheory

namespace Langlands.Scheme.Modules

/-- The canonical pullback tensor comparison is invertible for every scheme morphism. -/
def pullbackTensorComparisonIsIsoStatement : Prop :=
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
    IsIso (pullbackTensorComparison f)

end Langlands.Scheme.Modules
