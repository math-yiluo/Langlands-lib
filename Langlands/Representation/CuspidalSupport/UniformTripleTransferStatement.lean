import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Parabolic.ThreeBlockRefinementGeometry
import Langlands.Representation.Parabolic.RegroupingFactorEquivalences
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Category.Subquotients

/-! The isolated, uniform-rank local input for the repeated triple transfers. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual ordered tensor of three smooth rank-`d` representations,
on the Levi of the standard uniform three-block shape. -/
def uniformTripleTensor {d : ℕ} (hd : 0 < d) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear d F.Carrier) →
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear d F.Carrier) →
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear d F.Carrier) →
    SmoothRep.{0, uF, uV} ℂ ((threeBlocks d d d hd hd hd).Levi F.Carrier) :=
  letI := T.topology
  fun A B C => FiniteTensor.externalSmoothObject (threeBlockSmoothFamily A B C)

/-- The two local moves for an actual irreducible representation of rank
`d + (d + d)`. The third supercuspidal remains its supplied representative;
only its isomorphism class is required to repeat the first or second factor. -/
def UniformRepeatedCuspidalTripleJacquetTransfer : Prop :=
  letI := T.topology
  ∀ (d : ℕ) (hd : 0 < d)
    (E : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (d + (d + d)) F.Carrier))
    (A B C : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := d)),
    E.IsIrreducible → E.IsAdmissible → E.HasFiniteLength →
    SmoothRep.IsSubquotient (uniformTripleTensor F T hd A.obj B.obj C.obj)
      ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E) →
    A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
    (C.isoClass = B.isoClass →
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd B.obj A.obj C.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E)) ∧
    (C.isoClass = A.isoClass →
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd A.obj C.obj B.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E) ∨
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd B.obj A.obj C.obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E))

end Langlands.CuspidalSupport
