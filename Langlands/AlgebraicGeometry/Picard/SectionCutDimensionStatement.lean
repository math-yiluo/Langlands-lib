import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.KrullDimension.Basic

/-! # Topological bounds for principal section cuts -/

universe u

open AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Picard

/-- A proper closed subset of an irreducible space loses at least one
in dimension. A principal local quotient maps into the actual global
vanishing locus, giving its dimension as a lower bound. -/
def SectionCutDimensionStatement : Prop :=
  (∀ (T : Type u) [TopologicalSpace T] [IrreducibleSpace T]
    (Z : Set T), IsClosed Z → Z ≠ Set.univ →
      topologicalKrullDim Z + 1 ≤ topologicalKrullDim T) ∧
  (∀ (X : Scheme.{u}) (x : X) (c : Γ(X, ⊤)),
    ringKrullDim (X.presheaf.stalk x ⧸
      Ideal.span {X.presheaf.germ ⊤ x trivial c}) ≤
        topologicalKrullDim {y : X // y ∉ X.basicOpen c})

end Langlands.AlgebraicGeometry.Picard
