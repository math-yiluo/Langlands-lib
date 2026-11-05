import Langlands.Representation.Classification.SegmentHeadProductComparison
import Langlands.Representation.Classification.SegmentHeadReplacementDatum
import Langlands.Representation.Classification.SegmentBinaryHeadDatum
import Langlands.Representation.Classification.LinkedHeadDerivativeOccurrence
import Langlands.Representation.Classification.LinkedReplacementDerivativeObstruction
import Langlands.Representation.Classification.SegmentLinkageOrientationProof
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.UnlinkedSegmentHeadProduct
import Langlands.Representation.Classification.SegmentHeadProductPairReduction
import Langlands.Representation.Classification.SegmentGenericStatement
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-! The irreducibility criterion for arbitrary products of supplied special heads. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear Derivative PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

private theorem suppliedHeadCuspidalSupport
    (Δ : T.Segment.{uV,uF})
    (H : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hH : T.IsSegmentHead Δ H) :
    T.IsSupercuspidalSupport H Δ.cuspidalContent := by
  let := T.topology
  have hi := hH.isIrreducible
  obtain ⟨A,hA,-,q,hq⟩ := hH.isSegmentQuotient
  let R (i : Fin Δ.length) :
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := (Δ.member i.val).rank) :=
    SupercuspidalRep.twist (T.determinantPowerCharacter Δ.rank (i.val : ℝ))
      (T.isOpen_ker_determinantPowerCharacter _ _)
      (T.ker_determinant_le_ker_determinantPowerCharacter _ _) A
  have hR (i : Fin Δ.length) : (Δ.member i.val).IsRepresentedBy (R i) := by
    change T.supercuspidalClassRealPowerTwist Δ.rank (i.val : ℝ) A.isoClass =
      T.supercuspidalClassRealPowerTwist Δ.rank (i.val : ℝ) Δ.base.cls
    exact congrArg _ hA
  have hr : ∑ i : Fin Δ.length, (Δ.member i.val).rank = Δ.degree := by
    simp [Segment.member, Segment.degree]
  refine ⟨Δ.length,fun i => Δ.member i.val,rfl,hr,R,hR,hi,?_⟩
  change SmoothRep.IsSubquotient H (T.segmentInduced A.obj Δ.length Δ.rank_pos)
  exact (show SmoothRep.IsQuotient H (T.segmentInduced A.obj Δ.length Δ.rank_pos)
    from ⟨SmoothRep.ofHom q,hq⟩).isSubquotient

private theorem rankCast_irreducible {a b : ℕ} (h : a = b)
    (H : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hi : letI := T.topology; H.IsIrreducible) :
    letI := T.topology; ((generalLinearRankCast T h).obj H).IsIrreducible := by
  subst b
  exact hi

private theorem rankCast_support {a b : ℕ} (h : a = b)
    (H : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
    (s : Multiset (T.CuspidalDatum.{uV,uF}))
    (hs : T.IsSupercuspidalSupport H s) :
    T.IsSupercuspidalSupport ((generalLinearRankCast T h).obj H) s := by
  subst b
  exact hs

private theorem precedingHeadProduct_not_irreducible
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (hfree : CuspidalIntegralTwistFreeness.{uF,uV} F T)
    {Δ Γ U : T.Segment.{uV,uF}} {I : Option (T.Segment.{uV,uF})}
    (hp : Δ.Precedes Γ) (hs : Segment.IsUnionIntersectionReplacement Δ Γ U I)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (τ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier))
    (hπ : T.IsSegmentHead Δ π) (hτ : T.IsSegmentHead Γ τ) :
    letI := T.topology
    ¬ ((T.binaryNormalizedProductFunctor Δ.degree Γ.degree).obj (π,τ)).IsIrreducible := by
  let := T.topology
  intro hirr
  let b := segmentBinaryHeadDatum T Δ Γ π τ hπ hτ
  let r := segmentHeadReplacementDatum T hfree hp hs
  have hb : b.datum.induced.IsIrreducible :=
    (Weil.IsomorphismInvariance.irreducible_iff b.equivalence).mpr hirr
  let c := segmentHeadProductComparison T ψ (by have := Δ.degree_pos; omega)
    b.datum r.datum b.heads r.heads hb (b.content.trans r.content.symm)
  let obstruction := linkedReplacementDerivativeObstruction ψ hfree hp hs
  let o := linkedHeadDerivativeOccurrence T ψ obstruction.witness π τ hπ hτ
  let k := obstruction.witness.cut*Δ.rank+Γ.degree
  let J := generalLinearDerivative T ψ (Δ.degree+Γ.degree) k (Nat.le_of_lt o.order_lt)
  let D := (generalLinearRankCast T o.residual_rank.symm).obj o.head
  have hDo : SmoothRep.IsSubquotient D (J.obj b.datum.induced) :=
    (o.isSubquotient T ψ).of_iso_right
      (J.mapIso (SmoothRep.mkIso b.equivalence.symm))
  have hDr : SmoothRep.IsSubquotient D (J.obj r.datum.induced) :=
    smoothSubquotientTransitivity ℂ _ (J.obj r.datum.induced)
      (J.obj b.datum.induced) D hDo
      (c.derivative_isSubquotient T k (Nat.le_of_lt o.order_lt))
  have hDi : D.IsIrreducible :=
    rankCast_irreducible T o.residual_rank.symm o.head o.head_isHead.isIrreducible
  have hDs : T.IsSupercuspidalSupport D obstruction.witness.segment.cuspidalContent :=
    rankCast_support T o.residual_rank.symm o.head _
      (suppliedHeadCuspidalSupport T _ o.head o.head_isHead)
  exact obstruction.nonoccurrence (Δ.degree+Γ.degree) k o.order_lt
    r.datum r.heads r.segments r.datum.induced
    (SmoothRep.isSubquotient_iff_representation.mpr (WeylBranchPieces.IsSubquotient.refl _))
    D hDi obstruction.witness.segment.cuspidalContent hDs
    (Set.ext fun ρ => obstruction.witness.segment.mem_cuspidalContent ρ) hDr

private theorem twoBlockHeadProduct_not_irreducible
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (hfree : CuspidalIntegralTwistFreeness.{uF,uV} F T)
    {Δ Γ : T.Segment.{uV,uF}}
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (τ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier))
    (hπ : T.IsSegmentHead Δ π) (hτ : T.IsSegmentHead Γ τ)
    (hp : Δ.Precedes Γ)
    (d : T.SegmentProductDatum.{uV,uF} (Δ.degree+Γ.degree))
    (hd : d.blockList = [⟨Δ,π⟩,⟨Γ,τ⟩]) :
    letI := T.topology; ¬ d.induced.IsIrreducible := by
  let := T.topology
  intro hi
  let b := segmentBinaryHeadDatum T Δ Γ π τ hπ hτ
  have hb : b.datum.blockList = [⟨Δ,π⟩,⟨Γ,τ⟩] := by
    rfl
  let e := (d.inducedEquivOfBlockListEq b.datum (hd.trans hb.symm)).trans b.equivalence
  obtain ⟨U,I,hs⟩ := Segment.exists_unionIntersectionReplacement hfree hp
  exact precedingHeadProduct_not_irreducible T ψ hfree hp hs π τ hπ hτ
    (LengthTwo.isIrreducible_of_equiv e hi)

private theorem segmentHeadProduct_isUnlinked
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (hfree : CuspidalIntegralTwistFreeness.{uF,uV} F T)
    {n : ℕ} (d : T.SegmentProductDatum.{uV,uF} (n+1))
    (hd : d.HasSegmentHeads)
    (hirr : letI := T.topology; d.induced.IsIrreducible) :
    d.multisegment.IsUnlinked := by
  let := T.topology
  intro Δ hΔ Γ hΓ hlink
  obtain ⟨i,rfl⟩ : ∃ i, d.segments i = Δ := by
    simpa [SegmentProductDatum.multisegment] using hΔ
  obtain ⟨j,rfl⟩ : ∃ j, d.segments j = Γ := by
    simpa [SegmentProductDatum.multisegment] using hΓ
  have hij : i ≠ j := by
    rintro rfl
    exact (d.segments i).not_isLinked_self hlink
  rcases hlink.precedes_or_precedes with hp | hp
  · let pair := segmentHeadProductPairReduction T (Nat.succ_pos n) d hd hirr i j hij
    exact twoBlockHeadProduct_not_irreducible T ψ hfree (d.blocks i) (d.blocks j)
      (hd i) (hd j) hp pair.datum pair.blocks_eq pair.irreducible
  · let pair := segmentHeadProductPairReduction T (Nat.succ_pos n) d hd hirr j i hij.symm
    exact twoBlockHeadProduct_not_irreducible T ψ hfree (d.blocks j) (d.blocks i)
      (hd j) (hd i) hp pair.datum pair.blocks_eq pair.irreducible

/-- A product of supplied special segment heads is irreducible exactly when
its segment multiset is unlinked, with repeated segments allowed. -/
theorem segmentHeadProductIrreducibility
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentHeadProductIrreducibility.{uF,uV} F T := by
  let := T.topology
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  have hfree := cuspidalIntegralTwistFreeness.{uF,uV} F T
  intro n d hd
  exact ⟨fun hi => segmentHeadProduct_isUnlinked T ψ hfree d hd hi,
    fun hu => unlinkedSegmentHeadProduct_isIrreducible T ψ d hd hu⟩

end Langlands.Classification
