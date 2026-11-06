import Langlands.Representation.Classification.OrderedSegmentSquareIntegrableConversionProof
import Langlands.Representation.Classification.OrderedMultisegmentHeadReduction
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationReduction
import Langlands.Representation.Classification.SegmentSquareIntegrabilityStatement
import Langlands.Representation.Classification.LanglandsQuotients
import Mathlib.Data.List.FinRange
import Batteries.Data.List.Perm

/-!
# Reduction of ordered segment-head classification

The rank-zero case is unconditional. In positive rank the published conversion
reduces the classification to square-integrable Langlands classification and
uniqueness of the segment parameter of a special head.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

private theorem ofFn_matching {α : Type*} {r s : ℕ} (f : Fin r → α) (g : Fin s → α)
    (h : (List.ofFn f : Multiset α) = List.ofFn g) :
    ∃ e : Fin r ≃ Fin s, ∀ i, f i = g (e i) := by
  classical
  have hp : (List.ofFn f).Perm (List.ofFn g) := Quotient.exact h
  let e₀ : Fin (List.ofFn f).length ≃ Fin (List.ofFn g).length :=
    { toFun := hp.idxBij
      invFun := hp.symm.idxBij
      left_inv := hp.idxBij_symm_leftInverse_idxBij
      right_inv := hp.idxBij_symm_rightInverse_idxBij }
  let e := (finCongr (List.length_ofFn).symm).trans
    (e₀.trans (finCongr List.length_ofFn))
  refine ⟨e, fun i => ?_⟩
  have hi := hp.getElem_idxBij_eq_getElem ((finCongr (List.length_ofFn).symm) i)
  simp only [List.getElem_ofFn] at hi
  exact (congrArg f (Fin.ext rfl)).trans
    (hi.symm.trans (congrArg g (Fin.ext rfl)))

private theorem ofFn_eq_of_matching {α : Type*} {r s : ℕ}
    (f : Fin r → α) (g : Fin s → α) (e : Fin r ≃ Fin s)
    (h : ∀ i, f i = g (e i)) :
    (List.ofFn f : Multiset α) = List.ofFn g := by
  have hrs : r = s := by simpa using Fintype.card_congr e
  subst s
  have hf : f = g ∘ e := funext h
  rw [hf]
  exact Quotient.sound (Equiv.Perm.ofFn_comp_perm e g)

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem segmentProductDatum_length_rankZero
    (d : T.SegmentProductDatum.{max uF uV, uF} 0) : d.length = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  exact Fin.elim0 (d.shape.indexEquiv ⟨⟨0, h⟩, ⟨0, (d.segments ⟨0, h⟩).degree_pos⟩⟩)

/-- Every rank-zero segment datum has empty multisegment. -/
theorem segmentProductDatum_multisegment_rankZero
    (d : T.SegmentProductDatum.{max uF uV, uF} 0) : d.multisegment = 0 := by
  exact (Multiset.coe_eq_zero _).mpr
    (List.ofFn_eq_nil_iff.mpr (segmentProductDatum_length_rankZero F T d))

/-- All segment data of rank zero are equal, since both families are empty. -/
theorem segmentProductDatum_eq_rankZero
    (d d' : T.SegmentProductDatum.{max uF uV, uF} 0) : d = d' := by
  have hd := segmentProductDatum_length_rankZero F T d
  have hd' := segmentProductDatum_length_rankZero F T d'
  rcases d with ⟨r, Δ, h, B⟩
  rcases d' with ⟨s, Δ', h', B'⟩
  dsimp at hd hd'
  subst r
  subst s
  have hΔ : Δ = Δ' := funext fun i => Fin.elim0 i
  subst Δ'
  have hB : B = B' := funext fun i => Fin.elim0 i
  subst B'
  rfl

/-- The ordered segment-head classification holds in rank zero without any
classification or analytic premise. Only the weak quotient relations are used. -/
theorem orderedMultisegmentHeadClassification_rankZero
    (d d' : T.SegmentProductDatum.{max uF uV, uF} 0)
    (π π' : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
    (hπ : d.IsLanglandsQuotient π) (hπ' : d'.IsLanglandsQuotient π') :
    d.multisegment = d'.multisegment ↔ Nonempty (π ≅ π') := by
  let := T.topology
  have hd := segmentProductDatum_eq_rankZero F T d d'
  subst d'
  constructor
  · intro _
    exact nonempty_iso_of_isIrreducibleHead.{uF, max uF uV}
      (S := d.induced) (ρ := d.induced)
      (orderedMultisegmentHead_rankZero.{uF, uV} F T d hπ.1 hπ.2.1).2.2 hπ.2.2 hπ'.2.2
  · intro _
    rfl

/-- For actual segment heads, parameter uniqueness is exactly the implication
from rank isomorphism to equality of segments. The reverse uses the canonical
head of one segment and requires no parameter-uniqueness premise. -/
theorem segmentHeads_rankIso_iff_eq
    (hu : SegmentSpecialParameterUniqueness.{uF, uV} F T)
    {Δ Δ' : T.Segment.{max uF uV, uF}}
    {π : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    {π' : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ'.degree F.Carrier)}
    (hπ : T.IsSegmentHead Δ π) (hπ' : T.IsSegmentHead Δ' π') :
    (letI := T.topology; RankIso π π') ↔ Δ = Δ' := by
  let := T.topology
  constructor
  · rintro ⟨h, e⟩
    exact hu Δ Δ' h π π' hπ hπ' e
  · intro h
    subst Δ'
    obtain ⟨e⟩ := hπ.nonempty_iso_segmentHead
    obtain ⟨e'⟩ := hπ'.nonempty_iso_segmentHead
    exact RankIso.of_iso (e ≪≫ e'.symm)

private theorem rankIso_of_index_eq {ι : Type*} {m : ι → ℕ}
    (A : letI := T.topology;
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m i) F.Carrier))
    {i j : ι} (h : i = j) : letI := T.topology; RankIso (A i) (A j) := by
  let := T.topology
  subst j
  exact RankIso.refl _

/-- The all-rank target reduces to the two displayed classification premises.
Conversion of the actual products is supplied by its published proof. -/
def OrderedMultisegmentHeadClassificationReductionStatement : Prop :=
  SquareIntegrableLanglandsClassification.{uF, uV} F T →
    SegmentSpecialParameterUniqueness.{uF, uV} F T →
      OrderedMultisegmentHeadClassification.{uF, uV} F T

/-- Proof of the sufficient-condition statement, retaining both premises. -/
theorem orderedMultisegmentHeadClassification_of_squareIntegrable
    : OrderedMultisegmentHeadClassificationReductionStatement.{uF, uV} F T := by
  intro hc hu
  let := T.topology
  intro n d d' π π' hπ hπ'
  cases n with
  | zero => exact orderedMultisegmentHeadClassification_rankZero F T d d' π π' hπ hπ'
  | succ n =>
    obtain ⟨a, ⟨j⟩, σ, hσ⟩ :=
      orderedSegmentSquareIntegrableConversion.{uF, uV} F T
        (n + 1) (Nat.succ_pos n) d hπ.1 hπ.2.1
    obtain ⟨b, ⟨j'⟩, τ, hτ⟩ :=
      orderedSegmentSquareIntegrableConversion.{uF, uV} F T
        (n + 1) (Nat.succ_pos n) d' hπ'.1 hπ'.2.1
    have hσ' : ∀ i, RankIso (d.blocks i) (a.blocks (σ i)) := hσ
    have hτ' : ∀ i, RankIso (d'.blocks i) (b.blocks (τ i)) := hτ
    have hqa : a.IsLanglandsQuotient π := hπ.2.2.of_equiv (SmoothRep.equivOfIso j)
    have hqb : b.IsLanglandsQuotient π' := hπ'.2.2.of_equiv (SmoothRep.equivOfIso j')
    have hclass := hc (n + 1) (Nat.succ_pos n) a b π π' hqa hqb
    constructor
    · intro h
      obtain ⟨e, he⟩ := ofFn_matching d.segments d'.segments h
      apply hclass.mpr
      refine ⟨σ.symm.trans (e.trans τ), fun k => ?_⟩
      have hleft : RankIso (a.blocks k) (d.blocks (σ.symm k)) :=
        (rankIso_of_index_eq F T a.blocks (σ.apply_symm_apply k).symm).trans
          (hσ' (σ.symm k)).symm
      have hmid : RankIso (d.blocks (σ.symm k)) (d'.blocks (e (σ.symm k))) :=
        (segmentHeads_rankIso_iff_eq F T hu (hπ.2.1 _) (hπ'.2.1 _)).mpr (he _)
      exact hleft.trans (hmid.trans (hτ' _))
    · intro h
      obtain ⟨e, he⟩ := hclass.mp h
      have he' : ∀ k, RankIso (a.blocks k) (b.blocks (e k)) := he
      apply ofFn_eq_of_matching d.segments d'.segments (σ.trans (e.trans τ.symm))
      intro i
      apply (segmentHeads_rankIso_iff_eq F T hu (hπ.2.1 i) (hπ'.2.1 _)).mp
      have hright : RankIso (b.blocks (e (σ i))) (d'.blocks (τ.symm (e (σ i)))) :=
        (rankIso_of_index_eq F T b.blocks (τ.apply_symm_apply (e (σ i))).symm).trans
          (hτ' (τ.symm (e (σ i)))).symm
      exact (hσ' i).trans ((he' (σ i)).trans hright)

end Langlands.Classification
