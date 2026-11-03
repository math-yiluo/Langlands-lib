import Langlands.Representation.Classification.SegmentHeadProductShiftedSupport
import Langlands.Representation.Classification.SegmentHeadProductTopDerivative
import Langlands.Representation.Derivative.GeneralLinearHighestDerivativeOrder
import Langlands.Representation.Derivative.GeneralLinearHighestDerivativeUntwistedQuotient
import Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthProof

/-! # Highest derivatives of constituents of unlinked special-head products -/

noncomputable section

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear Derivative PadicField.TopologicalData
open CuspidalProductContragredient

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Choose highest positive derivative data for an irreducible constituent of
an unlinked product of supplied special heads, retaining that its order is the
whole ambient rank. -/
def chooseUnlinkedSegmentHeadProductHighestDerivativeOrder {n : ℕ}
    (d : T.SegmentProductDatum.{uV, uF} (n + 1))
    (hd : d.HasSegmentHeads) (hunlinked : d.multisegment.IsUnlinked)
    (Q : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier))
    (hQ : letI := T.topology; Q.IsIrreducible)
    (hQd : letI := T.topology; SmoothRep.IsSubquotient Q d.induced) :
    {w : GeneralLinearHighestDerivativeOrderData T ψ Q // w.order = n + 1} := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1)
  let w := chooseGeneralLinearHighestDerivativeOrder T ψ (Nat.succ_pos n) Q
    (SegmentHeadSupport.nontrivial_of_isIrreducible hQ)
  refine ⟨w, ?_⟩
  by_contra horder
  have hle := w.le_rank
  have hr : 0 < n + 1 - w.order := by omega
  let := T.generalLinearTopologicalGroup (n + 1 - w.order)
  have hfinite := generalLinearDerivativeFiniteLength F T ψ (n + 1) w.order w.le_rank Q
    (hasFiniteLength_of_isIrreducible hQ)
  let v := chooseGeneralLinearHighestDerivativeUntwistedQuotient T ψ n w.order
    ⟨w.positive, w.le_rank⟩ Q w.nonzero hfinite w.higher_vanish
  let S := SmoothRep.subrepresentation
    ((generalLinearDerivative T ψ (n + 1) w.order w.le_rank).obj Q) v.constituent
  have hS : SmoothRep.IsSubquotient S
      ((generalLinearDerivative T ψ (n + 1) w.order w.le_rank).obj Q) :=
    isSubquotient_of_injective_of_surjective
      (SmoothRep.subtype _ v.constituent) (SmoothRep.subtype_injective _ v.constituent)
      (𝟙 _) Function.surjective_id
  have hE : SmoothRep.IsSubquotient v.target
      ((generalLinearDerivative T ψ (n + 1) w.order w.le_rank).obj Q.contragredient) :=
    isSubquotient_of_injective_of_surjective (𝟙 _) Function.injective_id
      v.quotient v.surjective
  let c := chooseSegmentHeadProductShiftedSupportData T ψ (Nat.succ_pos n) w.le_rank hr
    d hd Q hQd S v.target v.irreducible
    (v.target_irreducible (compactOpen_cofinal F T _)) hS hE
    (v.targetDualIso (compactOpen_cofinal F T _))
  obtain ⟨i, j, hij⟩ := c.exists_linked_pair hr
  exact hunlinked (d.segments i) (by simp [SegmentProductDatum.multisegment])
    (d.segments j) (by simp [SegmentProductDatum.multisegment]) hij

/-- Every irreducible actual subquotient of an unlinked supplied special-head
product has nonzero whole top derivative. -/
theorem unlinkedSegmentHeadProduct_topDerivativeNonvanishing {n : ℕ}
    (d : T.SegmentProductDatum.{uV, uF} (n + 1))
    (hd : d.HasSegmentHeads) (hunlinked : d.multisegment.IsUnlinked) :
    letI := T.topology
    ExactFunctorIrreducibility.NonvanishingOnIrreducibleSubquotients
      (generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl) d.induced := by
  let := T.topology
  intro Q hQ hQd
  obtain ⟨⟨k, hk, hpos, hnonzero, hhigh⟩, heq⟩ :=
    chooseUnlinkedSegmentHeadProductHighestDerivativeOrder T ψ d hd hunlinked Q hQ hQd
  dsimp only at heq
  subst k
  exact hnonzero

include ψ in
/-- An unlinked product of supplied special heads is irreducible. -/
theorem unlinkedSegmentHeadProduct_isIrreducible {n : ℕ}
    (d : T.SegmentProductDatum.{uV, uF} (n + 1))
    (hd : d.HasSegmentHeads) (hunlinked : d.multisegment.IsUnlinked) :
    letI := T.topology
    d.induced.IsIrreducible :=
  segmentHeadProductIsIrreducible_of_topDerivativeNonvanishing T ψ (Nat.succ_pos n) d hd
    (unlinkedSegmentHeadProduct_topDerivativeNonvanishing T ψ d hd hunlinked)

end Langlands.Classification
