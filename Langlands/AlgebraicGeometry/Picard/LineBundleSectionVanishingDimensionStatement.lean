import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Topology.KrullDimension

/-! # Dimension of the actual vanishing locus of a line-bundle section -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Picard

/-- A section of a line bundle on a smooth proper geometrically connected
field scheme, with both a frame point and a nonframe point, has vanishing
locus of dimension exactly one less than the relative dimension. -/
def LineBundleSectionVanishingDimensionStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ),
    SmoothOfRelativeDimension g f → IsProper f → GeometricallyConnected f →
      ∀ (L : LineBundle X) (s : Langlands.SchemeModule.GlobalSections L.obj),
        (∃ x : X, x ∈ Langlands.SchemeModule.trivializationOpen L.obj s) →
        (∃ x : X, x ∉ Langlands.SchemeModule.trivializationOpen L.obj s) →
          topologicalKrullDim
            {x : X // x ∉ Langlands.SchemeModule.trivializationOpen L.obj s} + 1 =
              (g : WithBot ℕ∞)

end Langlands.AlgebraicGeometry.Picard
