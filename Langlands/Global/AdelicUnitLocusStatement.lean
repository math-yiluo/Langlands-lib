import Langlands.Global.GlobalPlaceTopologyFacts
import Langlands.Global.CurvePlaceAdeleDiagonal
import Langlands.AlgebraicGeometry.PointTopology.AffineLinePuncture

/-! # Failure of openness for the actual adelic unit locus -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Three forms of the unit-locus obstruction for an actual value algebra. -/
def AffineLineUnitLocusObstruction (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] [TopologicalSpace S] : Prop :=
  ¬ IsOpen {s : S | IsUnit s} ∧
    ¬ IsClosed {s : S | ¬ IsUnit s} ∧
    ¬ IsOpen (X := RingPoint R (ringTest R (MvPolynomial Unit R)) S)
      (Set.range (fun p : RingPoint R (affineLinePuncture R) S =>
      (p ≫ affineLinePunctureι R :
        RingPoint R (ringTest R (MvPolynomial Unit R)) S)))

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The obstruction in the original full number-field adelic topology. -/
def NumberFieldUnitLocusStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    AffineLineUnitLocusObstruction K (Adeles K)

/-- The obstruction for actual function-field adeles with finite constants. -/
def CurvePlaceUnitLocusStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F],
    AffineLineUnitLocusObstruction F (CurvePlaceAdeleRing k F)

/-- Conrad's nonopen basic-open point image in both global-field characteristics. -/
def AdelicUnitLocusStatement : Prop :=
  NumberFieldUnitLocusStatement.{u} ∧ CurvePlaceUnitLocusStatement.{u}

end Langlands.Global
