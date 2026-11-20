import Langlands.Representation.Classification.IsobaricSum
import Langlands.Representation.Classification.LanglandsHeadProductSubquotientProof
import Langlands.Representation.Classification.MultisegmentHeadClassificationProof
import Langlands.Representation.Classification.MultisegmentHeadExistenceProof
import Langlands.Representation.Classification.SegmentHeadSupportCons
import Langlands.Representation.Induction.BinaryProductSubquotients
import Langlands.Representation.Induction.HeadTailBinaryProduct
import Langlands.Correspondence.UnramifiedNormalization

/-! The local isobaric sum occurs in normalized induction in the supplied block order. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory

namespace Langlands.PadicField.TopologicalData

open Classification Classification.SegmentHeadSupport GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private theorem head_rankCast {m n : ℕ} (h : m = n)
    {a : T.Multisegment.{max uF uV, uF}}
    {A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hA : a.IsLanglandsHead A) :
    letI := T.topology
    a.IsLanglandsHead ((Derivative.generalLinearRankCast T h).obj A) := by
  subst n
  exact hA

private theorem degree_sum {k : ℕ} (a : Fin k → T.Multisegment.{max uF uV, uF}) :
    (∑ i, a i).degree = ∑ i, (a i).degree :=
  map_sum (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom Segment.degree)) a Finset.univ

private theorem rankCast_transport_cancel {m n : ℕ} (h : m = n)
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) :
    letI := T.topology
    (h.symm ▸ (Derivative.generalLinearRankCast T h).obj A :
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) = A := by
  cases h
  rfl

private theorem singleBlock_headSubquotient {n : ℕ} (B : BlockShape n) (hB : B.length = 1)
    (a : Fin B.length → T.Multisegment.{max uF uV, uF})
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hσ : ∀ i, (a i).IsLanglandsHead (σ i)) (hA : (∑ i, a i).IsLanglandsHead A) :
    letI := T.topology
    SmoothRep.IsSubquotient A ((T.normalizedProductInductionFunctor B).obj σ) := by
  let := T.topology
  let i := B.singleBlockIndex hB
  have hsum : (∑ j, a j) = a i := by
    apply Finset.sum_eq_single i
    · intro j _ hj
      exact (hj (B.eq_singleBlockIndex hB j)).elim
    · simp
  let C := (Derivative.generalLinearRankCast T (B.singleBlock_size hB i)).obj (σ i)
  have hC : (a i).IsLanglandsHead C := head_rankCast T _ (hσ i)
  rw [hsum] at hA
  obtain ⟨e⟩ := (multisegmentHeadClassification.{uF, uV} F T n (a i) (a i) A C hA hC).mp rfl
  let σ' : ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier) :=
    fun j => (B.singleBlock_size hB j).symm ▸ C
  have hfamily : σ' = σ := by
    funext j
    have hj : j = i := B.eq_singleBlockIndex hB j
    subst j
    exact rankCast_transport_cancel T (B.singleBlock_size hB i) (σ i)
  let eF := (T.normalizedProductInductionFunctor B).mapIso (eqToIso hfamily.symm)
  let eC : (T.normalizedProductInductionFunctor B).obj σ' ≅ C :=
    SmoothRep.mkIso (Parabolic.equivTrans (T.normalizedProductInductionObjEquiv B σ')
      (T.singleBlockTransportedProductEquiv B hB C))
  exact SmoothRep.IsSubquotient.of_iso_right (isSubquotient_refl A) (e ≪≫ (eF ≪≫ eC).symm)

private theorem headSubquotient_product :
    letI := T.topology
    ∀ k {n : ℕ}, 0 < n → ∀ (B : BlockShape n), B.length = k →
      ∀ (a : Fin B.length → T.Multisegment.{max uF uV, uF})
        (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
        (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
        (∀ i, (a i).IsLanglandsHead (σ i)) → (∑ i, a i).IsLanglandsHead A →
          SmoothRep.IsSubquotient A ((T.normalizedProductInductionFunctor B).obj σ) := by
  let := T.topology
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro n hn B hlen a σ A hσ hA
    rcases k with _ | k
    · have : IsEmpty (Fin B.length) := ⟨fun i => by have := i.isLt; omega⟩
      have hn0 : n = 0 := by
        simpa only [Finset.univ_eq_empty, Finset.sum_empty] using B.sum_eq.symm
      omega
    rcases k with _ | k
    · exact singleBlock_headSubquotient T B hlen a σ A hσ hA
    · have hB : B.length = k + 2 := hlen
      let tailLabel := fun j => a (B.tailIndex hB j)
      let tailFactors := fun j => σ (B.tailIndex hB j)
      have hdegree : (∑ j, tailLabel j).degree = B.tailRank hB := by
        rw [degree_sum]
        apply Finset.sum_congr rfl
        intro j _
        exact Aubert.LanglandsHeadDuality.degree_of_isLanglandsHead.{uF, uV}
          F T (hσ (B.tailIndex hB j))
      obtain ⟨C, hC⟩ := multisegmentHeadExistence.{uF, uV} F T (∑ j, tailLabel j)
      let C' := (Derivative.generalLinearRankCast T hdegree).obj C
      have hC' : (∑ j, tailLabel j).IsLanglandsHead C' := head_rankCast T hdegree hC
      have htail := ih (k + 1) (by omega) (B.tailRank_pos hB) (B.tailShape hB)
        rfl tailLabel tailFactors C' (fun j => hσ (B.tailIndex hB j)) hC'
      have hsum : (∑ i, a i) = a (B.headIndex hB) + ∑ j, tailLabel j :=
        ((Equiv.sum_comp (finCongr hB.symm) a).symm).trans (Fin.sum_univ_succ _)
      let h := B.headRank_add_tailRank hB
      let A' := (Derivative.generalLinearRankCast T h.symm).obj A
      have hA' : (a (B.headIndex hB) + ∑ j, tailLabel j).IsLanglandsHead A' :=
        hsum ▸ head_rankCast T h.symm hA
      have hbinary := langlandsHeadProductSubquotient.{uF, uV} F T
        (B.headRank hB) (B.tailRank hB) (B.headRank_pos hB) (B.tailRank_pos hB)
        (a (B.headIndex hB)) (∑ j, tailLabel j) (σ (B.headIndex hB)) C' A'
        (hσ (B.headIndex hB)) hC' hA'
      rw [← T.binaryNormalizedProductFunctor_of_pos (B.headRank_pos hB) (B.tailRank_pos hB)]
        at hbinary
      have hproduct := T.binaryProduct_isSubquotient
        (isSubquotient_refl (σ (B.headIndex hB))) htail
      exact ((isSubquotient_rankCast_iff T h A _).mpr
        (isSubquotient_trans hbinary hproduct)).of_iso_right
          (T.headTailBinaryProductIso B hB σ).symm

/-- An isobaric sum is a subquotient of normalized induction of its blocks in
  their given order, with no unitarity or genericity hypothesis on the blocks. -/
theorem IsIsobaricSum.isSubquotient_normalizedProduct {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    {σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    {A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : T.IsIsobaricSum.{max uF uV, uF} σ A) :
    letI := T.topology
    Correspondence.IsSubquotientOf
      (T.normalizedProductInduced B (fun i => (σ i).representation)) A.representation := by
  let := T.topology
  obtain ⟨a, hσ, hA⟩ := h
  exact (SmoothRep.isSubquotient_iff_representation
    (D := A) (A := (T.normalizedProductInductionFunctor B).obj σ)).mp
    (headSubquotient_product T B.length hn B rfl a σ A hσ hA)

end Langlands.PadicField.TopologicalData
