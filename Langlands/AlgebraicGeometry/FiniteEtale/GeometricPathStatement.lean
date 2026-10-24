import Langlands.AlgebraicGeometry.FiniteEtale.Statements

open CategoryTheory

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- Existence of a path between two actual geometric finite fibre functors.
The coefficient fields may differ; only their universe is shared. -/
def GeometricPathExists {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S]
    {Ωs Ωt : Type u} [Field Ωs] [IsAlgClosed Ωs] [Field Ωt] [IsAlgClosed Ωt]
    (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y)) : Prop :=
  Nonempty (fiberFunctor s hs ≅ fiberFunctor t ht)

end Langlands.AlgebraicGeometry.FiniteEtale
