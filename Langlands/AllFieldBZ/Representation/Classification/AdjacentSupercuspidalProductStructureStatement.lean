import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwist
import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic
import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement

/-! The two ordered Jacquet factors of an adjacent cuspidal product. -/

namespace Langlands.AllFieldBZ.Classification

open Langlands.GeneralLinear LocalFieldPackage.TopologicalData

universe uF uV

/-- The actual normalized product of an adjacent supercuspidal pair has
length two with a unique nonzero proper subrepresentation. Its subobject
and quotient have the ordered and reversed normalized Jacquet modules. -/
def AdjacentSupercuspidalProductStructureStatement (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (r : ℕ) (hr : 0 < r)
    (A B : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)),
    (B.isoClass = T.supercuspidalClassRealPowerTwist r 1 A.isoClass ∨
      A.isoClass = T.supercuspidalClassRealPowerTwist r 1 B.isoClass) →
    let C := Shahidi.twoBlocks r r hr hr
    let X := Langlands.Classification.twoBlockFactors hr hr A.obj B.obj
    let Y := Langlands.Classification.twoBlockFactors hr hr B.obj A.obj
    let P := (T.normalizedProductInductionFunctor C).obj X
    HasCompositionSeriesLength P.obj 2 ∧
      (∃! S : Subrepresentation P.representation, S ≠ ⊥ ∧ S ≠ ⊤) ∧
      ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
        let U := SmoothRep.subrepresentation P S
        let Q := SmoothRep.quotient P S
        U.IsIrreducible ∧ Q.IsIrreducible ∧
          Nonempty (((T.normalizedJacquetFunctor C).obj U).representation.Equiv
            (FiniteTensor.externalSmoothObject X).representation) ∧
          Nonempty (((T.normalizedJacquetFunctor C).obj Q).representation.Equiv
            (FiniteTensor.externalSmoothObject Y).representation)

end Langlands.AllFieldBZ.Classification
