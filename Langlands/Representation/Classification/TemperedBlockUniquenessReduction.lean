import Langlands.Representation.Classification.TemperedBlockStatement
import Langlands.Representation.Classification.SegmentSquareIntegrabilityStatement
import Langlands.Representation.Classification.SegmentGenericStatement
import Langlands.Representation.Classification.LanglandsQuotients
import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Mathlib.Data.List.FinRange
import Batteries.Data.List.Perm

/-!
# A conditional reduction of tempered block uniqueness

The datum constructor transports supplied blocks to the degrees of their
segments. The final theorem derives tempered block uniqueness from three
explicit segment hypotheses; it does not establish those hypotheses.
-/

noncomputable section

open CategoryTheory Langlands.GeneralLinear

namespace Langlands.Classification.TemperedBlockUniquenessReduction

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

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Build the segment product using rank-transported supplied blocks. -/
def segmentProductOfPresentations {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology; ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (Δ : Fin B.length → T.Segment.{max uF uV,uF})
    (h : ∀ i, (Δ i).degree = B.size i) : T.SegmentProductDatum.{max uF uV,uF} n where
  length := B.length
  segments := Δ
  degree_sum := (Finset.sum_congr rfl fun i _ => h i).trans B.sum_eq
  blocks i := (h i).symm ▸ σ i

private theorem datum_induced {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology; ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (Δ : Fin B.length → T.Segment.{max uF uV,uF})
    (h : ∀ i, (Δ i).degree = B.size i) :
    letI := T.topology
    Nonempty ((segmentProductOfPresentations T B σ Δ h).induced ≅
      (T.normalizedProductInductionFunctor B).obj σ) := by
  let := T.topology
  rcases B with ⟨r, sizes, positive, sum_eq⟩
  dsimp at Δ h σ ⊢
  have hh : (fun i => (Δ i).degree) = sizes := funext h
  cases hh
  exact ⟨Iso.refl _⟩


private theorem equal_segment_heads_iso {Δ Δ' : T.Segment.{max uF uV,uF}}
    {a b : ℕ} (ha : Δ.degree = a) (hb : Δ'.degree = b) (hΔ : Δ = Δ')
    (π : letI := T.topology; SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
    (π' : letI := T.topology; SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hπ : T.IsSegmentHead Δ (ha.symm ▸ π))
    (hπ' : T.IsSegmentHead Δ' (hb.symm ▸ π'))
    (hab : a = b) : letI := T.topology; Nonempty ((hab ▸ π) ≅ π') := by
  subst Δ'
  subst a
  subst b
  obtain ⟨e⟩ := hπ.nonempty_iso_segmentHead
  obtain ⟨e'⟩ := hπ'.nonempty_iso_segmentHead
  exact ⟨e ≪≫ e'.symm⟩

private theorem datum_unlinked {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology; ∀ i,
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (Δ : Fin B.length → T.Segment.{max uF uV,uF})
    (h : ∀ i, (Δ i).degree = B.size i)
    (hu : ∀ i j, ¬ (Δ i).IsLinked (Δ j)) :
    (segmentProductOfPresentations T B σ Δ h).multisegment.IsUnlinked := by
  intro A hA A' hA'
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hA'
  exact hu i j

private theorem segmentHead_of_iso {Δ : T.Segment.{max uF uV,uF}}
    {π π' : letI := T.topology;
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentHead Δ π) (e : letI := T.topology; π ≅ π') :
    T.IsSegmentHead Δ π' := by
  let := T.topology
  obtain ⟨A, hA, hirr, q, hq, huniq⟩ := h
  let E := SmoothRep.equivOfIso e
  refine ⟨A, hA, (isIrreducible_iff_of_equiv E).mp hirr,
    E.toIntertwiningMap.comp q, E.surjective.comp hq, ?_⟩
  intro W _ _ ρ hρ f hf
  rw [huniq W ρ hρ f hf]
  ext x
  change q x = 0 ↔ E (q x) = 0
  exact ⟨fun hx => by rw [hx]; exact map_zero E,
    fun hx => E.injective (hx.trans (map_zero E).symm)⟩

private theorem segmentHead_eq_transport {Δ Δ' : T.Segment.{max uF uV,uF}}
    (hΔ : Δ = Δ') {a : ℕ} (h : Δ.degree = a) (h' : Δ'.degree = a)
    (π : letI := T.topology; SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hhead : T.IsSegmentHead Δ (h.symm ▸ π)) :
    T.IsSegmentHead Δ' (h'.symm ▸ π) := by
  subst Δ'
  exact hhead

private theorem squareIntegrable_cast {a b : ℕ} (h : a = b)
    (π : letI := T.topology; SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hπ : letI := T.topology; T.IsSquareIntegrable π.representation) :
    letI := T.topology; T.IsSquareIntegrable (h ▸ π).representation := by
  subst b
  exact hπ

private theorem cast_iso {a b k : ℕ} (ha : k = a) (hb : k = b) (h : a = b)
    (π : letI := T.topology; SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
    (π' : letI := T.topology; SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier))
    (e : letI := T.topology; Nonempty ((h ▸ π) ≅ π')) :
    letI := T.topology; Nonempty ((ha.symm ▸ π) ≅ (hb.symm ▸ π')) := by
  subst a
  subst b
  exact e

private theorem ofFn_eq_of_matching {α : Type*} {r s : ℕ}
    (f : Fin r → α) (g : Fin s → α) (e : Fin r ≃ Fin s)
    (h : ∀ i, f i = g (e i)) :
    (List.ofFn f : Multiset α) = List.ofFn g := by
  have hrs : r = s := by simpa using Fintype.card_congr e
  subst s
  have hf : f = g ∘ e := funext h
  rw [hf]
  exact Quotient.sound (Equiv.Perm.ofFn_comp_perm e g)

variable
  (hc : SegmentEssentialSquareIntegrableClassification.{uF,uV} F T)
  (hu : GenericSegmentProductUniqueness.{uF,uV} F T)
  (hnonlink : letI := T.topology
    ∀ (Δ Δ' : T.Segment.{max uF uV,uF})
      (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
      (π' : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ'.degree F.Carrier)),
      T.IsSegmentHead Δ π → T.IsSegmentHead Δ' π' →
      T.IsSquareIntegrable π.representation → T.IsSquareIntegrable π'.representation →
      ¬ Δ.IsLinked Δ')

include hc hu hnonlink in
private theorem match_of_induced_iso {n : ℕ} (B C : BlockShape (n+1))
    (σ : letI := T.topology; ∀ i,
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (τ : letI := T.topology; ∀ j,
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (C.size j) F.Carrier))
    (hσ : letI := T.topology; ∀ i, Representation.IsIrreducible (σ i).representation ∧
      T.IsSquareIntegrable (σ i).representation ∧ IsUnitarizable (σ i).representation)
    (hτ : letI := T.topology; ∀ j, Representation.IsIrreducible (τ j).representation ∧
      T.IsSquareIntegrable (τ j).representation ∧ IsUnitarizable (τ j).representation)
    (hiso : letI := T.topology;
      Nonempty ((T.normalizedProductInductionFunctor B).obj σ ≅
        (T.normalizedProductInductionFunctor C).obj τ)) :
    letI := T.topology
    ∃ (e : Fin B.length ≃ Fin C.length) (h : ∀ i, B.size i = C.size (e i)),
      ∀ i, Nonempty ((h i ▸ σ i) ≅ τ (e i)) := by
  classical
  let := T.topology
  have hs := fun i => (hc (B.size i) (B.positive i) (σ i) (hσ i).1).mp
    (hσ i).2.1.isEssentiallySquareIntegrable
  have ht := fun j => (hc (C.size j) (C.positive j) (τ j) (hτ j).1).mp
    (hτ j).2.1.isEssentiallySquareIntegrable
  choose Δ hd hh using hs
  choose Δ' hd' hh' using ht
  let d := segmentProductOfPresentations T B σ Δ hd
  let d' := segmentProductOfPresentations T C τ Δ' hd'
  have hdu : d.multisegment.IsUnlinked := datum_unlinked T B σ Δ hd fun i j => by
    apply hnonlink (Δ i) (Δ j) _ _ (hh i) (hh j)
    · exact squareIntegrable_cast T (hd i).symm _ (hσ i).2.1
    · exact squareIntegrable_cast T (hd j).symm _ (hσ j).2.1
  have hdu' : d'.multisegment.IsUnlinked := datum_unlinked T C τ Δ' hd' fun i j => by
    apply hnonlink (Δ' i) (Δ' j) _ _ (hh' i) (hh' j)
    · exact squareIntegrable_cast T (hd' i).symm _ (hτ i).2.1
    · exact squareIntegrable_cast T (hd' j).symm _ (hτ j).2.1
  obtain ⟨ed⟩ := datum_induced T B σ Δ hd
  obtain ⟨ed'⟩ := datum_induced T C τ Δ' hd'
  obtain ⟨eI⟩ := hiso
  have hm := (hu n d d' hh hh' hdu hdu').mp ⟨ed ≪≫ eI ≪≫ ed'.symm⟩
  obtain ⟨e, he⟩ := ofFn_matching Δ Δ' hm
  have hr : ∀ i, B.size i = C.size (e i) := fun i =>
    (hd i).symm.trans ((congrArg (fun A => A.degree) (he i)).trans (hd' (e i)))
  exact ⟨e, hr, fun i =>
    equal_segment_heads_iso T (hd i) (hd' (e i)) (he i) _ _ (hh i) (hh' (e i)) (hr i)⟩

include hc hu hnonlink in
private theorem induced_iso_of_match {n : ℕ} (B C : BlockShape (n+1))
    (σ : letI := T.topology; ∀ i,
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (τ : letI := T.topology; ∀ j,
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (C.size j) F.Carrier))
    (hσ : letI := T.topology; ∀ i, Representation.IsIrreducible (σ i).representation ∧
      T.IsSquareIntegrable (σ i).representation ∧ IsUnitarizable (σ i).representation)
    (e : Fin B.length ≃ Fin C.length) (hr : ∀ i, B.size i = C.size (e i))
    (he : letI := T.topology; ∀ i, Nonempty ((hr i ▸ σ i) ≅ τ (e i))) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor B).obj σ ≅
      (T.normalizedProductInductionFunctor C).obj τ) := by
  classical
  let := T.topology
  have hs := fun i => (hc (B.size i) (B.positive i) (σ i) (hσ i).1).mp
    (hσ i).2.1.isEssentiallySquareIntegrable
  choose Δ hd hh using hs
  let Δ' : Fin C.length → T.Segment.{max uF uV,uF} := fun j => Δ (e.symm j)
  have hd' : ∀ j, (Δ' j).degree = C.size j := fun j =>
    (hd (e.symm j)).trans ((hr (e.symm j)).trans (congrArg C.size (e.apply_symm_apply j)))
  have hh' : ∀ j, T.IsSegmentHead (Δ' j) ((hd' j).symm ▸ τ j) := by
    intro j
    obtain ⟨i, rfl⟩ := e.surjective j
    have H := segmentHead_of_iso T (hh i)
      (cast_iso T (hd i) ((hd i).trans (hr i)) (hr i) _ _ (he i)).some
    exact segmentHead_eq_transport T (Δ := Δ i) (Δ' := Δ' (e i))
      (congrArg Δ (e.symm_apply_apply i)).symm
      ((hd i).trans (hr i)) (hd' (e i)) _ H
  let d := segmentProductOfPresentations T B σ Δ hd
  let d' := segmentProductOfPresentations T C τ Δ' hd'
  have hdu : d.multisegment.IsUnlinked := datum_unlinked T B σ Δ hd fun i j => by
    apply hnonlink (Δ i) (Δ j) _ _ (hh i) (hh j)
    · exact squareIntegrable_cast T (hd i).symm _ (hσ i).2.1
    · exact squareIntegrable_cast T (hd j).symm _ (hσ j).2.1
  have hm : d.multisegment = d'.multisegment :=
    ofFn_eq_of_matching Δ Δ' e (fun i => by simp [Δ'])
  have hdu' : d'.multisegment.IsUnlinked := hm ▸ hdu
  obtain ⟨eI⟩ := (hu n d d' hh hh' hdu hdu').mpr hm
  obtain ⟨ed⟩ := datum_induced T B σ Δ hd
  obtain ⟨ed'⟩ := datum_induced T C τ Δ' hd'
  exact ⟨ed.symm ≪≫ eI ≪≫ ed'⟩

end Langlands.Classification.TemperedBlockUniquenessReduction

namespace Langlands.Classification

universe uF uV

/-- Algebraic reduction: the three segment inputs remain explicit assumptions. -/
theorem temperedBlockUniqueness_of_segment_inputs
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (hc : SegmentEssentialSquareIntegrableClassification.{uF,uV} F T)
    (hu : GenericSegmentProductUniqueness.{uF,uV} F T)
    (hnonlink : letI := T.topology
      ∀ (Δ Δ' : T.Segment.{max uF uV,uF})
        (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
        (π' : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ'.degree F.Carrier)),
        T.IsSegmentHead Δ π → T.IsSegmentHead Δ' π' →
        T.IsSquareIntegrable π.representation → T.IsSquareIntegrable π'.representation →
        ¬ Δ.IsLinked Δ') :
    TemperedBlockUniqueness.{uF,uV} F T := by
  let := T.topology
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
    intro B C σ τ hσ hτ
    constructor
    · exact TemperedBlockUniquenessReduction.match_of_induced_iso T hc hu hnonlink
        B C σ τ hσ hτ
    · rintro ⟨e, hr, he⟩
      exact TemperedBlockUniquenessReduction.induced_iso_of_match T hc hu hnonlink
        B C σ τ hσ e hr he

end Langlands.Classification
