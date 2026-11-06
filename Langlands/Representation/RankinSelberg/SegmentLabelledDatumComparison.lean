import Langlands.Representation.Classification.TemperedBlockUniquenessReduction
import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.LanglandsQuotients
import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof
import Langlands.Representation.Aubert.SegmentSocleHeadLengthOne
import Langlands.Combinatorics.FiniteOccurrenceMatching

/-!
# Segment labellings of square-integrable Langlands data

A segment labelling of square-integrable Langlands data `d` attaches to each block
`π_i` a segment `Δ_i` of the same degree of which `π_i` is the segment head. Every
datum has one (Bernstein's theorem, proved in the Library). Two consequences used
in Henniart's §4: under the square-integrable Langlands classification, irreducible
quotients of data with the same multiset of labels are isomorphic; and an
irreducible quotient of data labelled by a single segment of length one is
supercuspidal.
-/

noncomputable section

open CategoryTheory Langlands.GeneralLinear

namespace Langlands.RankinSelberg

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A segment labelling of the blocks of `d`: each block `π_i` is, after the
transport along `deg Δ_i = n_i`, a segment head of `Δ_i`. -/
def IsSegmentLabelling {n : ℕ} (d : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n)
    (Δ : Fin d.shape.length → T.Segment.{max uF uV, uF}) : Prop :=
  ∀ i, ∃ h : (Δ i).degree = d.shape.size i, T.IsSegmentHead (Δ i) (h.symm ▸ d.blocks i)

/-- Every square-integrable Langlands datum has a segment labelling. -/
theorem exists_isSegmentLabelling {n : ℕ}
    (d : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n) :
    ∃ Δ : Fin d.shape.length → T.Segment.{max uF uV, uF}, IsSegmentLabelling d Δ := by
  let := T.topology
  have h := fun i =>
    (Classification.segmentEssentialSquareIntegrableClassification.{uF, uV} F T
      (d.shape.size i) (d.shape.positive i) (d.blocks i) (d.irreducible i)).mp
      (d.essentiallySquareIntegrable i)
  choose Δ hΔ using h
  exact ⟨Δ, hΔ⟩

/-- Under the square-integrable Langlands classification, irreducible quotients of
two square-integrable Langlands data whose segment labellings have the same
multiset of segments are isomorphic. -/
theorem nonempty_iso_of_segmentLabelling_eq
    (hC : Classification.SquareIntegrableLanglandsClassification.{uF, uV} F T)
    {n : ℕ} (hn : 0 < n) (d d' : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n)
    (π π' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hd : d.IsLanglandsQuotient π) (hd' : d'.IsLanglandsQuotient π')
    (Δ : Fin d.shape.length → T.Segment.{max uF uV, uF}) (hΔ : IsSegmentLabelling d Δ)
    (Δ' : Fin d'.shape.length → T.Segment.{max uF uV, uF}) (hΔ' : IsSegmentLabelling d' Δ')
    (heq : (Finset.univ.val.map Δ : Multiset (T.Segment.{max uF uV, uF})) =
      Finset.univ.val.map Δ') :
    letI := T.topology; Nonempty (π ≅ π') := by
  let := T.topology
  choose hdeg hhead using hΔ
  choose hdeg' hhead' using hΔ'
  rw [Fin.univ_val_map, Fin.univ_val_map] at heq
  obtain ⟨e, he⟩ := Langlands.Combinatorics.exists_equiv_of_ofFn_multiset_eq Δ Δ' heq
  refine (hC n hn d d' π π' hd hd').mpr ⟨e, fun i => ?_⟩
  have hr : d.shape.size i = d'.shape.size (e i) :=
    (hdeg i).symm.trans ((congrArg (fun A => A.degree) (he i)).trans (hdeg' (e i)))
  exact ⟨hr, Langlands.Classification.TemperedBlockUniquenessReduction.equal_segment_heads_iso
    T (hdeg i) (hdeg' (e i)) (he i) _ _ (hhead i) (hhead' (e i)) hr⟩

/-- A segment head of a segment of length one is supercuspidal. -/
theorem isSupercuspidal_of_isSegmentHead_of_length_eq_one {Δ : T.Segment.{max uF uV, uF}}
    (hΔ : Δ.length = 1)
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentHead Δ π) :
    letI := T.topology; IsSupercuspidal π.representation := by
  let := T.topology
  obtain ⟨A, -, hπirr, q, hq, -⟩ := h
  have hI : (T.segmentInduced A.obj Δ.length Δ.rank_pos).IsIrreducible ∧
      IsSupercuspidal (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation := by
    have hm : ∀ m, m = 1 →
        (T.segmentInduced A.obj m Δ.rank_pos).IsIrreducible ∧
          IsSupercuspidal (T.segmentInduced A.obj m Δ.rank_pos).representation := by
      intro m hm
      subst m
      exact T.segmentInducedOne_supercuspidal A Δ.rank_pos
    exact hm Δ.length hΔ
  let := hI.1
  have hq0 : q ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := CentralEigenspaceSplitting.exists_ne_zero_of_isIrreducible hπirr
    obtain ⟨w, hw⟩ := hq v
    apply hv
    rw [← hw, hz]
    rfl
  have hqi := (Representation.IsIrreducible.injective_or_eq_zero q).resolve_right hq0
  exact GeneralLinear.isSupercuspidal_of_equiv (q.ofBijective ⟨hqi, hq⟩) hI.2

/-- The transported form of `isSupercuspidal_of_isSegmentHead_of_length_eq_one`. -/
theorem isSupercuspidal_of_isSegmentHead_cast {Δ : T.Segment.{max uF uV, uF}}
    (hΔ : Δ.length = 1) {k : ℕ} (hk : Δ.degree = k)
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier)}
    (h : T.IsSegmentHead Δ (hk.symm ▸ π)) :
    letI := T.topology; IsSupercuspidal π.representation := by
  subst k
  exact isSupercuspidal_of_isSegmentHead_of_length_eq_one hΔ h

private theorem isSupercuspidal_rankTransport {r n : ℕ} (h : r = n)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear r F.Carrier) V) :
    letI := T.topology
    IsSupercuspidal ρ →
      IsSupercuspidal (ρ.comp
        (GeneralLinear.reindex (R := F.Carrier) (finCongr h)).symm.toMonoidHom) := by
  let := T.topology
  subst n
  intro hρ
  rw [GeneralLinear.reindex_finCongr_rfl]
  change IsSupercuspidal (ρ.comp (MonoidHom.id _))
  simpa only [MonoidHom.comp_id] using hρ

private theorem isIrreducible_rankTransport {r n : ℕ} (h : r = n)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear r F.Carrier) V)
    (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible (ρ.comp
      (GeneralLinear.reindex (R := F.Carrier) (finCongr h)).symm.toMonoidHom) := by
  subst n
  rw [GeneralLinear.reindex_finCongr_rfl]
  change Representation.IsIrreducible (ρ.comp (MonoidHom.id _))
  simpa only [MonoidHom.comp_id] using hρ

/-- An irreducible quotient of square-integrable Langlands data whose segment
labelling is a single segment of length one is supercuspidal. -/
theorem isSupercuspidal_of_segmentLabelling_eq_singleton {n : ℕ}
    (d : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n)
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hd : d.IsLanglandsQuotient π)
    (Δ : Fin d.shape.length → T.Segment.{max uF uV, uF}) (hΔ : IsSegmentLabelling d Δ)
    (Γ : T.Segment.{max uF uV, uF}) (hΓ : Γ.length = 1)
    (h : (Finset.univ.val.map Δ : Multiset (T.Segment.{max uF uV, uF})) = {Γ}) :
    letI := T.topology; IsSupercuspidal π.representation := by
  let := T.topology
  have hlen : d.shape.length = 1 := by
    simpa using congrArg Multiset.card h
  let i := d.shape.singleBlockIndex hlen
  have hi : Δ i = Γ := by
    have hmem : Δ i ∈ (Finset.univ.val.map Δ : Multiset (T.Segment.{max uF uV, uF})) :=
      Multiset.mem_map_of_mem Δ (Finset.mem_univ i)
    rw [h] at hmem
    exact Multiset.mem_singleton.mp hmem
  obtain ⟨hdeg, hhead⟩ := hΔ i
  have hblock : IsSupercuspidal (d.blocks i).representation :=
    isSupercuspidal_of_isSegmentHead_cast (hi ▸ hΓ) hdeg hhead
  let e := T.singleBlockNormalizedProductEquiv d.shape hlen
    (fun j => (d.blocks j).representation) (fun j => (d.blocks j).isSmooth) i
  have hIsc : IsSupercuspidal d.induced.representation :=
    GeneralLinear.isSupercuspidal_of_equiv e.symm
      (isSupercuspidal_rankTransport _ _ hblock)
  have hIirr : Representation.IsIrreducible d.induced.representation :=
    (Langlands.isIrreducible_iff_of_equiv e).mpr
      (isIrreducible_rankTransport _ _ (d.irreducible i))
  obtain ⟨hπirr, q, hq⟩ := hd
  let := hIirr
  have hq0 : q ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := CentralEigenspaceSplitting.exists_ne_zero_of_isIrreducible hπirr
    obtain ⟨w, hw⟩ := hq v
    apply hv
    rw [← hw, hz]
    rfl
  have hqi := (Representation.IsIrreducible.injective_or_eq_zero q).resolve_right hq0
  exact GeneralLinear.isSupercuspidal_of_equiv (q.ofBijective ⟨hqi, hq⟩) hIsc

end Langlands.RankinSelberg
