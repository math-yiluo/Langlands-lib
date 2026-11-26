import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwist
import Langlands.AllFieldBZ.Representation.Induction.BinaryProduct

/-! Reducibility for actual adjacent supercuspidal factors. -/

namespace Langlands.AllFieldBZ.Classification

open Langlands.GeneralLinear LocalFieldPackage.TopologicalData

universe uF uV

/-- Normalized induction of two supercuspidal factors related by the
residue-normalized determinant twist is reducible in either order. -/
def AdjacentSupercuspidalProductReducibilityStatement (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (r : ℕ), 0 < r →
    ∀ A B : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r),
      (B.isoClass = T.supercuspidalClassRealPowerTwist r 1 A.isoClass ∨
        A.isoClass = T.supercuspidalClassRealPowerTwist r 1 B.isoClass) →
      ¬ ((T.binaryNormalizedProductFunctor r r).obj (A.obj, B.obj)).IsIrreducible

end Langlands.AllFieldBZ.Classification
