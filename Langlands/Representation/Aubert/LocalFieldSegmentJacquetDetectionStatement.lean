import Langlands.AllFieldBZ.Representation.Classification.OrderedSegmentProducts
import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic
import Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor
import Langlands.Representation.Smooth.IrreducibleGrothendieckProof
import Langlands.VirtualRepresentation.PositiveSupport

/-! Detection on the constituent support of an actual segment induction. -/

noncomputable section

namespace Langlands.Aubert.LocalFieldGraded

open GeneralLinear SmoothRep VirtualRepresentation
open SmoothRep.IrreducibleGrothendieckProof
open AllFieldBZ (LocalFieldPackage)
open AllFieldBZ.LocalFieldPackage.TopologicalData

universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- Actual normalized Jacquet restriction expressed in the two irreducible bases. -/
def jacquetOnFactors {n : ℕ} (B : BlockShape n)
    (hL : letI := T.topology;
      PreservesFiniteLength (T.normalizedJacquetFunctor.{uF,max uF uV} B))
    (hE : letI := T.topology;
      PreservesFiniteLengthShortExact (T.normalizedJacquetFunctor.{uF,max uF uV} B)) :
    letI := T.topology
    SmoothRep.IrreducibleLattice.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier) →ₗ[ℤ]
      SmoothRep.IrreducibleLattice.{0,uF,max uF uV} ℂ (B.Levi F.Carrier) :=
  letI := T.topology
  factorMap.comp ((SmoothRep.FiniteLengthGrothendieckGroup.map
    (T.normalizedJacquetFunctor B) hL hE).comp
    (realizeIrreducibles ℂ (GeneralLinear n F.Carrier)))

/-- Full equal-block Jacquet restriction reflects effectivity on virtual classes
supported on the actual constituents of the increasing segment product. -/
def LocalFieldSegmentJacquetDetectionStatement : Prop :=
  letI := T.topology
  ∀ (Δ : Segment.{uV,uF} T)
    (A : SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank)),
    Δ.base.IsRepresentedBy A →
    let B := BlockShape.uniform Δ.length Δ.rank Δ.rank_pos
    let σ := FiniteTensor.externalSmoothObject (fun i : Fin B.length => (T.segmentFactor Δ A i).obj)
    let P := (T.normalizedParabolicInductionFunctor.{uF,uV} B).obj σ
    ∀ (hP : P.HasFiniteLength)
      (hL : PreservesFiniteLength (T.normalizedJacquetFunctor.{uF,max uF uV} B))
      (hE : PreservesFiniteLengthShortExact (T.normalizedJacquetFunctor.{uF,max uF uV} B))
      (w : SmoothRep.IrreducibleLattice.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      w.support ⊆ (compositionFactors ⟨P,hP⟩).support →
      jacquetOnFactors T B hL hE w ∈ effective → w ∈ effective

end Langlands.Aubert.LocalFieldGraded
