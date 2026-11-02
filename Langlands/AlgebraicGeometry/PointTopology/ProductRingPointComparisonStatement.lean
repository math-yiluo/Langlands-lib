import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints

/-!
# Source-qualified product-ring point comparison

The injectivity, affine surjectivity and quasi-compact/local-factor surjectivity
clauses have independent hypotheses.
-/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Conrad (3.6.2), including the affine case used in the proof of surjectivity. -/
def ProductRingPointComparisonStatement : Prop :=
  ∀ (C : Type u) [CommRing C] (ι : Type u) (R : ι → Type u)
    [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
    (X : Over (Spec (CommRingCat.of C))),
    (∀ [QuasiSeparatedSpace X.left], Function.Injective (productPointMap C R X)) ∧
    (∀ [IsAffine X.left], Function.Surjective (productPointMap C R X)) ∧
    (∀ [CompactSpace X.left] [∀ i, IsLocalRing (R i)],
      Function.Surjective (productPointMap C R X))

end Langlands.AlgebraicGeometry.PointTopology
