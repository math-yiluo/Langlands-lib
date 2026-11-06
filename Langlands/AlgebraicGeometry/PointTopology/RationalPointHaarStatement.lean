import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Regularity of Haar measures on actual rational points -/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Second countability and measure regularity for finite-type affine group points. -/
def RationalPointHaarRegularityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    letI : MeasurableSpace (RationalPoint F G.X) := borel (RationalPoint F G.X)
    SecondCountableTopology (RationalPoint F G.X) ∧
      ∀ mu : Measure (RationalPoint F G.X), mu.IsHaarMeasure → mu.Regular ∧ mu.InnerRegular

end Langlands.AlgebraicGeometry.PointTopology
