import Langlands.Representation.Classification.SegmentProductCuspidalMembers
import Langlands.Representation.Parabolic.InducedMapSurjectivity
import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.SegmentCuspidalContent
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Tensor.ExternalMapSurjectivityProof
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof

/-! # Actual cuspidal quotients of segment-head products with independent universes -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false



namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Actual cuspidal member representatives and a surjective map from their
normalized product to a supplied product of segment heads. Segment bases stay
in `uV`, independently of `uF`. -/
structure SegmentHeadProductCuspidalQuotientData {n : ℕ}
    (d : T.SegmentProductDatum.{uV,uF} n) where
  length : ℕ
  members : Fin length → T.CuspidalDatum.{uV,uF}
  rank_sum : ∑ i, (members i).rank = n
  content_eq : (List.ofFn members : Multiset _) = d.multisegment.cuspidalContent
  representatives : letI := T.topology
    ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := (members i).rank)
  represents : ∀ i, (members i).IsRepresentedBy (representatives i)
  quotientMap : letI := T.topology
    T.cuspidalProductInduced members rank_sum representatives ⟶ d.induced
  surjective : letI := T.topology
    Function.Surjective (SmoothRep.hom quotientMap)

open SegmentProductCuspidalEmbedding in
/-- Construct the actual quotient from the primitive head quotient maps,
retaining every segment and member occurrence. -/
def segmentHeadProductCuspidalQuotient {n : ℕ}
    (d : T.SegmentProductDatum.{uV,uF} n) (hd : d.HasSegmentHeads) :
    SegmentHeadProductCuspidalQuotientData T d := by
  classical
  let := T.topology
  have hq (j : Fin d.length) := (hd j).isSegmentQuotient
  choose A hA hquot using hq
  choose hblock q hsurj using hquot
  let source := fun j => T.segmentInduced (A j).obj (d.segments j).length
    (d.segments j).rank_pos
  let Q : (T.normalizedProductInductionFunctor d.shape).obj source ⟶ d.induced :=
    SmoothRep.ofHom (T.normalizedProductInducedMap d.shape q)
  have hQ : Function.Surjective (SmoothRep.hom Q) :=
    normalizedProductMap_surjective F T d.shape source d.blocks q hsurj
  let e := Classical.choice (memberInducedIso d A)
  exact ⟨_, memberFamily d, memberFamily_sum d,
    memberFamily_content d, memberRepresentatives d A,
    memberRepresentatives_represent d A hA, e.hom ≫ Q,
    hQ.comp (SmoothRep.hom_hom_surjective e)⟩

/-- An irreducible supplied product of segment heads has exactly their
cuspidal member multiset as a support, for independent base universe `uV`. -/
theorem segmentHeadProductCuspidalSupportIndependent {n : ℕ}
    (d : T.SegmentProductDatum.{uV,uF} n) (hd : d.HasSegmentHeads)
    (hirr : letI := T.topology; d.induced.IsIrreducible) :
    T.IsSupercuspidalSupport d.induced d.multisegment.cuspidalContent := by
  let := T.topology
  let C := segmentHeadProductCuspidalQuotient T d hd
  refine ⟨C.length, C.members, C.content_eq, C.rank_sum,
    C.representatives, C.represents, hirr, ?_⟩
  exact SmoothRep.IsQuotient.isSubquotient ⟨C.quotientMap, C.surjective⟩

end Langlands.Classification
