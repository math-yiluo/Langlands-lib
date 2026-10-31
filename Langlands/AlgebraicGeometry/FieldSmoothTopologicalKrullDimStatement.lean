import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Topology.KrullDimension

/-! # The dimension of a quasi-compact smooth scheme over a field is at most its relative
dimension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- If `X` is a quasi-compact scheme and `f : X ⟶ Spec k` is smooth of relative dimension
`g` over a field `k`, then the underlying topological space of `X` has Krull dimension at
most `g`. -/
def FieldSmoothTopologicalKrullDimStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ),
    SmoothOfRelativeDimension g f → CompactSpace X →
      topologicalKrullDim X ≤ (g : WithBot ℕ∞)

end Langlands.AlgebraicGeometry
