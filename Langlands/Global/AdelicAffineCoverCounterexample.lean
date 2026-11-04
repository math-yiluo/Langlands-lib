import Langlands.AlgebraicGeometry.PointTopology.AffineLinePuncture
import Langlands.Global.Adelic
import Langlands.Global.CurvePlaceAdeleDiagonal
import Langlands.Global.CurvePlaceExtension

/-! # An actual binary affine-line cover and explicit adelic points -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]

/-- The actual opens D(t) and D(1-t) of the affine line, indexed by Bool. -/
def affineLineBinaryOpen : Bool → (ringTest R (MvPolynomial Unit R)).left.Opens
  | false => affineLinePuncturedOpen R
  | true => PrimeSpectrum.basicOpen (1 - MvPolynomial.X ())

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The union of the actual point images of the two specified affine opens. -/
def affineLineBinaryPointUnion :
    Set (RingPoint R (ringTest R (MvPolynomial Unit R)) S) :=
  ⋃ b : Bool, Set.range (openPointMap R (ringTest R (MvPolynomial Unit R)) S
    (affineLineBinaryOpen R b))

/-- The point image of the singleton open cover consisting of the whole affine line. -/
def affineLineTopPointUnion :
    Set (RingPoint R (ringTest R (MvPolynomial Unit R)) S) :=
  Set.range (openPointMap R (ringTest R (MvPolynomial Unit R)) S ⊤)

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- Zero at every infinite place, one at every finite place. -/
def numberFieldAffineCoverCoordinate : Adeles K := (0, 1)

/-- The actual relative affine-line point evaluating its coordinate at (0,1). -/
def numberFieldAffineCoverPoint :
    RingPoint K (ringTest K (MvPolynomial Unit K)) (Adeles K) :=
  (affineLinePointEquiv K (Adeles K)).symm (numberFieldAffineCoverCoordinate K)

end NumberField

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- Zero at the chosen actual place over t=0, one at every other actual curve place.
Every coordinate is integral, so this is an element of the actual restricted product. -/
def curvePlaceAffineCoverCoordinate : CurvePlaceAdeleRing k F := by
  classical
  refine ⟨fun v => if v = curvePlaceReference k F then 0 else 1, ?_⟩
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  split
  · exact (curvePlaceCompletionIntegers v).zero_mem
  · exact (curvePlaceCompletionIntegers v).one_mem

variable [Finite k]

/-- The actual relative affine-line point with the zero/one adelic coordinate,
using the original function-field diagonal action. -/
def curvePlaceAffineCoverPoint :
    RingPoint F (ringTest F (MvPolynomial Unit F)) (CurvePlaceAdeleRing k F) :=
  (affineLinePointEquiv F (CurvePlaceAdeleRing k F)).symm
    (curvePlaceAffineCoverCoordinate k F)

end Curve

end Langlands.Global
