import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange
import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-! # Actual integral points and generic-fiber points over a DVR -/

noncomputable section
universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped WithZero

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- With their independently constructed chart topologies, actual integral
points map continuously and openly to generic-fiber points; separatedness
additionally makes this an open embedding. -/
def DvrSchemePointProperties : Prop :=
  letI : Valued K ℤᵐ⁰ := Valued.mk' ((IsDiscreteValuationRing.maximalIdeal R).valuation K)
  letI : TopologicalSpace R := TopologicalSpace.induced (algebraMap R K) inferInstance
  ∀ (X : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType X.hom],
    letI : TopologicalSpace (RingPoint R X R) := schemePointTopology R X R
    letI : TopologicalSpace (RingPoint K (ringBaseChange R K X) K) :=
      schemePointTopology K (ringBaseChange R K X) K
    let f := ringPointBaseChangeEquiv R K K X ∘
      RingPoint.changeRing (X := X) (Algebra.ofId R K)
    Continuous f ∧ IsOpenMap f ∧ (∀ [IsSeparated X.hom], IsOpenEmbedding f)

end Langlands.AlgebraicGeometry.PointTopology
