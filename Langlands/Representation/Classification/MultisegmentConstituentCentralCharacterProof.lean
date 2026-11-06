import Langlands.Representation.Classification.MultisegmentConstituentCompatibilityStatement
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Batteries.Data.List.Perm

/-!
# The scalar action on multisegment socles and Langlands heads

A multisegment relation is witnessed by a segment product datum ordering the
multiset. Its segments are a reindexing of the given family, every block is a
segment head or socle and so carries the segment central character, the
normalized product induction carries the product character, and the final
representation inherits it through the actual quotient or embedding.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

/-- Two families with the same multiset of values differ by a reindexing. -/
theorem exists_equiv_of_ofFn_eq {α : Type*} {r s : ℕ} (f : Fin r → α) (g : Fin s → α)
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

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A segment head or socle of a segment equal to `Δ` has the segment central
character of `Δ`. -/
theorem hasScalarCharacter_of_segmentHead_or_socle :
    letI := T.topology
    ∀ (Δ' : T.Segment.{uV, uF})
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ'.degree F.Carrier)),
      (T.IsSegmentHead Δ' π ∨ T.IsSegmentSocle Δ' π) →
      ∀ (Δ : T.Segment.{uV, uF}), Δ' = Δ → ∀ (ω : F.Carrierˣ →* ℂˣ)
        (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)),
        Δ.base.IsRepresentedBy A →
        HasScalarCharacter A.obj.representation GeneralLinear.scalar ω →
        HasScalarCharacter π.representation GeneralLinear.scalar
          (ω ^ Δ.length *
            (T.determinantPowerCharacter Δ.degree (((Δ.length : ℝ) - 1) / 2)).comp
              GeneralLinear.scalar) := by
  let := T.topology
  intro Δ' π hπ Δ hΔ ω A hA hω
  subst hΔ
  refine (segmentConstituentCentralCharacter.{uF, uV} F T Δ' ω A hA hω).2.2 π ?_
  rcases hπ with h | h
  · exact Or.inr h.isSegmentQuotient
  · exact Or.inl h.isSegmentSubrepresentation

/-- Both multisegment constituents have the product of the segment central
characters. -/
theorem multisegmentConstituentCentralCharacter :
    MultisegmentConstituentCentralCharacter.{uF, uV} F T := by
  let := T.topology
  intro r Δ A ω hA hω ωΔ a n _ π hπ
  -- The common witness: a segment product datum whose blocks are segment
  -- constituents and whose induced representation maps onto, or contains, `π`.
  obtain ⟨d, hda, hblocks, hπd⟩ : ∃ d : T.SegmentProductDatum.{uV, uF} n,
      d.multisegment = a ∧
      (∀ j, T.IsSegmentHead (d.segments j) (d.blocks j) ∨
        T.IsSegmentSocle (d.segments j) (d.blocks j)) ∧
      ((∃ q : d.induced.representation.IntertwiningMap π.representation,
          Function.Surjective q) ∨
        ∃ i : π.representation.IntertwiningMap d.induced.representation,
          Function.Injective i) := by
    rcases hπ with ⟨d, hda, -, hs, -, i, hi, -⟩ | ⟨d, hda, -, hh, -, q, hq, -⟩
    · exact ⟨d, hda, fun j => Or.inr (hs j), Or.inr ⟨i, hi⟩⟩
    · exact ⟨d, hda, fun j => Or.inl (hh j), Or.inl ⟨q, hq⟩⟩
  obtain ⟨e, he⟩ := exists_equiv_of_ofFn_eq d.segments Δ hda
  have hblock : ∀ j, HasScalarCharacter (d.blocks j).representation
      GeneralLinear.scalar (ωΔ (e j)) := fun j =>
    hasScalarCharacter_of_segmentHead_or_socle F T (d.segments j) (d.blocks j) (hblocks j)
      (Δ (e j)) (he j) (ω (e j)) (A (e j)) (hA (e j)) (hω (e j))
  have hind : HasScalarCharacter d.induced.representation GeneralLinear.scalar
      (∏ j, ωΔ (e j)) :=
    T.hasScalarCharacter_normalizedProductInduced d.shape hblock
  rw [Equiv.prod_comp e ωΔ] at hind
  rcases hπd with ⟨q, hq⟩ | ⟨i, hi⟩
  · exact hind.of_surjective q hq
  · exact hind.of_injective i hi

end Langlands.Classification
