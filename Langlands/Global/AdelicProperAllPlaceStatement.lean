import Langlands.Global.AllPlaceSchemePoints
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Full-product comparison for proper adelic scheme points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- The actual all-place map for a proper function-field scheme is a homeomorphism
for the topology from any specified finite-type arithmetic spread. -/
def CurvePlaceProperAllPlaceStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y) [IsProper Y.hom],
    letI := curvePlaceSpreadAdelePointTopology k F S X Y e
    letI := curvePlaceLocalPointTopology k F Y
    IsHomeomorph (curvePlaceAdelePointMap k F Y)

/-- The full number-field product includes every archimedean completion. -/
def NumberFieldProperAllPlaceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y) [IsProper Y.hom],
    letI := numberFieldSpreadAdelePointTopology K S X Y e
    letI := numberFieldLocalPointTopology K Y
    IsHomeomorph (numberFieldAdelePointMap K Y)

/-- The proper-scheme extension of the full-product comparison in Example 4.3. -/
def AdelicProperAllPlaceStatement : Prop :=
  CurvePlaceProperAllPlaceStatement.{u} ∧ NumberFieldProperAllPlaceStatement.{u}

end Langlands.Global
