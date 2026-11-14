import Langlands.Representation.Classification.LanglandsSubrepresentationStatement
import Langlands.Representation.Classification.SegmentHeadProductContragredient
import Langlands.Representation.Classification.MultisegmentConstituentContragredientProof
import Langlands.Representation.Classification.MultisegmentHeadClassificationProof
import Langlands.Representation.Classification.OrderedMultisegmentHeadExistenceProof
import Langlands.Representation.Classification.OrderedMultisegmentHeadReduction
import Langlands.Representation.Classification.TrivialGroupQuotient
import Langlands.Representation.Classification.HeadTargetTransport
import Langlands.Representation.Classification.SegmentSocleDecreasingHead
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.Classification.OrderedSegmentHeadProductIndependence

/-!
# Langlands heads as subrepresentations of reversed standard modules: proof

Proof of `LanglandsSubrepresentationRealization` by smooth duality. The same-order
dual datum `d.dual` is precedence-ordered exactly when no later segment of `d` precedes
an earlier one. An embedding into `d.induced` dualizes to a quotient of `d.dual.induced`,
and the dual of the head quotient of `d.dual.induced` is an embedding into `d.induced`.
Rank zero is handled directly through the one-dimensional empty product.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

namespace LanglandsSubrepresentation

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The reversed precedence condition on `d` is the precedence order of the
same-order dual datum. -/
theorem dual_isPrecedenceOrdered {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)
    (hrev : ∀ i j, i < j → ¬ (d.segments j).Precedes (d.segments i)) :
    d.dual.IsPrecedenceOrdered := by
  intro i j hij hp
  exact hrev i j hij ((Segment.precedes_dual_iff _ _).mp hp)

/-- The multisegment of the same-order dual datum is the dual multisegment. -/
theorem dual_multisegment {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n) :
    d.dual.multisegment = d.multisegment.map Segment.dual := by
  rw [SegmentProductDatum.multisegment, SegmentProductDatum.multisegment, Multiset.map_coe,
    List.map_ofFn]
  rfl

/-- Segment duality is an involution on multisegments. -/
theorem map_dual_map_dual (a : T.Multisegment.{uV, uF}) :
    (a.map Segment.dual).map Segment.dual = a := by
  simp [Multiset.map_map]

/-- A rank-zero segment-product datum has no segments. -/
theorem rankZero_index_elim (d : T.SegmentProductDatum.{uV, uF} 0) (i : Fin d.length) :
    False := by
  have h := d.degree_sum
  have hpos := (d.segments i).degree_pos
  have hle : (d.segments i).degree ≤ ∑ j, (d.segments j).degree :=
    Finset.single_le_sum (f := fun j => (d.segments j).degree)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- Segment duality is an involution on the ordered segment list of a datum. -/
theorem dual_dual_segments_list {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n) :
    List.ofFn d.dual.dual.segments = List.ofFn d.segments := by
  show List.ofFn (fun i : Fin d.length => (d.segments i).dual.dual) = List.ofFn d.segments
  simp only [Segment.dual_dual]

/-- Embeddings transport along an isomorphism of the target. -/
theorem isSubrepresentation_of_iso_right {H : Type*} [Group H] [TopologicalSpace H]
    {A B C : SmoothRep ℂ H} (f : SmoothRep.IsSubrepresentation A B) (e : B ≅ C) :
    SmoothRep.IsSubrepresentation A C := by
  obtain ⟨f, hf⟩ := f
  exact ⟨f ≫ e.hom, (SmoothRep.equivOfIso e).injective.comp hf⟩

/-- Embeddings transport along an isomorphism of the source. -/
theorem isSubrepresentation_of_iso_left {H : Type*} [Group H] [TopologicalSpace H]
    {A B C : SmoothRep ℂ H} (f : SmoothRep.IsSubrepresentation B C) (e : A ≅ B) :
    SmoothRep.IsSubrepresentation A C := by
  obtain ⟨f, hf⟩ := f
  exact ⟨e.hom ≫ f, hf.comp (SmoothRep.equivOfIso e).injective⟩

/-- **Clause 2, positive rank.** An irreducible subrepresentation of the product is a
Langlands head of its multisegment. -/
theorem isLanglandsHead_of_subrepresentation {n : ℕ} (hn : 0 < n)
    (d : T.SegmentProductDatum.{max uF uV, uF} n) (hh : d.HasSegmentHeads)
    (hrev : ∀ i j, i < j → ¬ (d.segments j).Precedes (d.segments i))
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (hsub : letI := T.topology; SmoothRep.IsSubrepresentation σ d.induced) :
    d.multisegment.IsLanglandsHead σ := by
  let := T.topology
  let : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
    fun k => T.generalLinearTopologicalGroup k
  obtain ⟨j, hj⟩ := hsub
  have hG := GeneralLinear.compactOpen_cofinal F T n
  have hσadm : σ.IsAdmissible := (CuspidalSupport.cuspidalEmbedding F T n σ hσ).1
  have hσv : σ.contragredient.IsIrreducible :=
    (SmoothRep.isIrreducible_contragredient_iff hG σ hσadm).mpr hσ
  let E := SmoothRep.equivOfIso (d.contragredientInducedIso hh)
  have hE : Function.Surjective E.symm.toIntertwiningMap := E.symm.surjective
  have hs := contragredientMap_surjective_of_injective_of_compact_cofinal hG σ.isSmooth
    d.induced.isSmooth (SmoothRep.hom j) hj
  have ho := dual_isPrecedenceOrdered d hrev
  obtain ⟨π₀, -, -, h₀⟩ := orderedMultisegmentHeadExistence.{uF, uV} F T n d.dual ho hh.dual
  obtain ⟨e⟩ := h₀.nonempty_equiv_of_quotient_of_surjective E.symm.toIntertwiningMap hE hσv
    (contragredientMap (SmoothRep.hom j)) hs
  have hhead : d.dual.IsLanglandsHead σ.contragredient :=
    ⟨ho, hh.dual, h₀.of_targetEquiv e.symm⟩
  have h₂ := SegmentProductDatum.IsLanglandsHead.contragredient d.dual hn hhead
  refine ⟨d.dual.dualReverse, ?_, h₂.1, h₂.2.1,
    h₂.2.2.of_targetEquiv (SmoothRep.equivOfIso (SmoothRep.bidualIso hG σ hσadm)).symm⟩
  rw [SegmentProductDatum.dualReverse_multisegment, dual_multisegment, map_dual_map_dual]

/-- **Clause 1, positive rank.** Every Langlands head of the multisegment embeds into
the product. -/
theorem isSubrepresentation_of_isLanglandsHead {n : ℕ} (hn : 0 < n)
    (d : T.SegmentProductDatum.{max uF uV, uF} n) (hh : d.HasSegmentHeads)
    (hrev : ∀ i j, i < j → ¬ (d.segments j).Precedes (d.segments i))
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : d.multisegment.IsLanglandsHead π) :
    letI := T.topology
    SmoothRep.IsSubrepresentation π d.induced := by
  let := T.topology
  let : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
    fun k => T.generalLinearTopologicalGroup k
  have hG := GeneralLinear.compactOpen_cofinal F T n
  have ho := dual_isPrecedenceOrdered d hrev
  obtain ⟨π₀, -, -, h₀⟩ := orderedMultisegmentHeadExistence.{uF, uV} F T n d.dual ho hh.dual
  obtain ⟨hπ₀, q₀, hq₀, -⟩ := h₀
  have hπ₀adm : π₀.IsAdmissible := (CuspidalSupport.cuspidalEmbedding F T n π₀ hπ₀).1
  have hπ₀v : π₀.contragredient.IsIrreducible :=
    (SmoothRep.isIrreducible_contragredient_iff hG π₀ hπ₀adm).mpr hπ₀
  obtain ⟨B⟩ := nonempty_headProduct_iso_of_segmentList_eq F T (dual_dual_segments_list d)
    hh.dual.dual hh
  have h₁ : SmoothRep.IsSubrepresentation π₀.contragredient d.dual.induced.contragredient :=
    ⟨SmoothRep.ofHom (contragredientMap q₀), contragredientMap_injective_of_surjective q₀ hq₀⟩
  have h₂ : SmoothRep.IsSubrepresentation π₀.contragredient d.induced :=
    isSubrepresentation_of_iso_right
      (isSubrepresentation_of_iso_right h₁ (d.dual.contragredientInducedIso hh.dual)) B
  have hsub : d.multisegment.IsLanglandsHead π₀.contragredient :=
    isLanglandsHead_of_subrepresentation hn d hh hrev π₀.contragredient hπ₀v h₂
  obtain ⟨e⟩ := (multisegmentHeadClassification.{uF, uV} F T n _ _ π π₀.contragredient
    hπ hsub).mp rfl
  exact isSubrepresentation_of_iso_left h₂ e

/-- **Rank zero, clause 1.** -/
theorem isSubrepresentation_of_isLanglandsHead_rankZero
    (d : T.SegmentProductDatum.{max uF uV, uF} 0) (hh : d.HasSegmentHeads)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
    (hπ : d.multisegment.IsLanglandsHead π) :
    letI := T.topology
    SmoothRep.IsSubrepresentation π d.induced := by
  let := T.topology
  have ho : d.IsPrecedenceOrdered := fun i _ _ _ => (rankZero_index_elim d i).elim
  have hd₀ : d.multisegment.IsLanglandsHead d.induced :=
    ⟨d, rfl, orderedMultisegmentHead_rankZero F T d ho hh⟩
  obtain ⟨e⟩ := (multisegmentHeadClassification.{uF, uV} F T 0 _ _ π d.induced
    hπ hd₀).mp rfl
  let e' := SmoothRep.equivOfIso e
  exact ⟨SmoothRep.ofHom e'.toIntertwiningMap, e'.injective⟩

/-- **Rank zero, clause 2.** Every irreducible representation of `GL_0` is the head of
the empty product. -/
theorem isLanglandsHead_of_irreducible_rankZero
    (d : T.SegmentProductDatum.{max uF uV, uF} 0) (hh : d.HasSegmentHeads)
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible) :
    d.multisegment.IsLanglandsHead σ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup 0
  have ho : d.IsPrecedenceOrdered := fun i _ _ _ => (rankZero_index_elim d i).elim
  obtain ⟨-, -, h₀⟩ := orderedMultisegmentHead_rankZero F T d ho hh
  obtain ⟨-, q, hq⟩ := isIrreducibleQuotient_of_subsingleton_linearEquiv
    d.induced.representation σ.representation hσ
    (rankZeroNormalizedProductLinearEquiv F T d.shape
      (fun i => (d.blocks i).representation))
  obtain ⟨e⟩ := h₀.nonempty_equiv_of_quotient hσ q hq
  exact ⟨d, rfl, ho, hh, h₀.of_targetEquiv e.symm⟩

end LanglandsSubrepresentation

open LanglandsSubrepresentation in
/-- **Langlands heads in reversed standard modules.** For a segment-product datum whose
blocks are segment heads and in which no later segment precedes an earlier one, the
Langlands heads of its multisegment are exactly the irreducible subrepresentations of its
normalized product, in the sense of the two implications of
`LanglandsSubrepresentationRealization`. -/
theorem langlandsSubrepresentationRealization :
    LanglandsSubrepresentationRealization.{uF, uV} := by
  intro p _ F T n d hh hrev
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun π hπ => isSubrepresentation_of_isLanglandsHead_rankZero d hh π hπ,
      fun σ hσ _ => isLanglandsHead_of_irreducible_rankZero d hh σ hσ⟩
  · exact ⟨fun π hπ => isSubrepresentation_of_isLanglandsHead hn d hh hrev π hπ,
      fun σ hσ hsub => isLanglandsHead_of_subrepresentation hn d hh hrev σ hσ hsub⟩

end Langlands.Classification
