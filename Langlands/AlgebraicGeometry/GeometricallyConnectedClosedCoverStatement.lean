import Langlands.AlgebraicGeometry.IrreducibleComponentIncidence
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Geometric connectedness from an actual finite closed cover -/

noncomputable section

universe u v

open Set CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ComponentIncidence

/-- For a finite closed cover by geometrically connected schemes over a field,
 geometric connectedness of the covered scheme is exactly connected incidence. -/
def FiniteClosedGeometricallyConnectedCoverCriterion : Prop :=
  ∀ (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) {ι : Type v} [Finite ι]
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (g i)],
    (⋃ i, Set.range (g i)) = Set.univ →
    (∀ i, GeometricallyConnected (g i ≫ f)) →
    (GeometricallyConnected f ↔
      IntersectionChainConnected (fun i => Set.range (g i)))

end Langlands.AlgebraicGeometry.ComponentIncidence
