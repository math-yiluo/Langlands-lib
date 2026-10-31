import Langlands.Representation.Classification.SegmentConstituentStatement
import Langlands.Representation.Classification.CanonicalConstituents

/-! Strong heads of decreasing inductions for supplied actual segment socles. -/

noncomputable section

namespace Langlands.Classification

universe uG uV

variable {G : Type uG} [Group G]
  {V W W' : Type uV} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
  {ρ : Representation ℂ G V} {π : Representation ℂ G W}
  {π' : Representation ℂ G W'}

/-- A target equivalence preserves a strong irreducible head, including its
uniqueness as a quotient object. -/
theorem IsIrreducibleHead.of_targetEquiv (h : IsIrreducibleHead ρ π)
    (e : π.Equiv π') : IsIrreducibleHead ρ π' := by
  obtain ⟨hπ, q, hq, hu⟩ := h
  refine ⟨(Weil.IsomorphismInvariance.irreducible_iff e).mp hπ,
    e.toIntertwiningMap.comp q, e.surjective.comp hq, ?_⟩
  intro W'' _ _ σ hσ q' hq'
  rw [hu W'' σ hσ q' hq']
  ext v
  simp only [LinearMap.mem_ker]
  exact (map_eq_zero_iff e e.injective).symm

/-- Every actual irreducible quotient of a representation with a strong head is
equivalent to that head. -/
theorem IsIrreducibleHead.nonempty_equiv_of_quotient
    (h : IsIrreducibleHead ρ π) (hπ' : Representation.IsIrreducible π')
    (q : ρ.IntertwiningMap π') (hq : Function.Surjective q) :
    Nonempty (π'.Equiv π) := by
  obtain ⟨e⟩ := h.nonempty_headEquiv
  exact ⟨(headEquivOfSurjective q hq (h.headKernel_eq π' hπ' q hq)).symm.trans e⟩

/-- Irreducible quotients of any actual quotient of the source have its strong
head's isomorphism type. -/
theorem IsIrreducibleHead.nonempty_equiv_of_quotient_of_surjective
    {M : Type uV} [AddCommGroup M] [Module ℂ M]
    {σ : Representation ℂ G M} (h : IsIrreducibleHead ρ π)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (hπ' : Representation.IsIrreducible π')
    (q : σ.IntertwiningMap π') (hq : Function.Surjective q) :
    Nonempty (π'.Equiv π) :=
  h.nonempty_equiv_of_quotient hπ' (q.comp f) (hq.comp hf)

end Langlands.Classification

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Supplied strong segment socles are equivalent, independently of their chosen
supercuspidal representatives. -/
theorem IsSegmentSocle.nonempty_equiv
    {Δ : Segment.{uV,uF} T}
    {π π' : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSocle Δ π) (hπ' : T.IsSegmentSocle Δ π') :
    let := T.topology
    Nonempty (π.representation.Equiv π'.representation) := by
  let := T.topology
  obtain ⟨A, hA, h⟩ := hπ
  have h' := (T.isSegmentSocle_iff Δ π' A hA).mp hπ'
  obtain ⟨e⟩ := h.nonempty_socleEquiv
  obtain ⟨e'⟩ := h'.nonempty_socleEquiv
  exact ⟨e.trans e'.symm⟩

/-- Individual-segment constituent existence makes any supplied strong segment
socle the strong head of every decreasing induction of that segment. -/
theorem IsSegmentSocle.isIrreducibleHead_down
    (hex : SegmentZelevinskyConstituentExistence.{uF,uV} F T)
    {Δ : Segment.{uV,uF} T}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSocle Δ π)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    let := T.topology
    IsIrreducibleHead
      (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation
      π.representation := by
  let := T.topology
  obtain ⟨π₀, hπ₀, hhead⟩ := hex Δ
  obtain ⟨e⟩ := hπ₀.nonempty_equiv hπ
  exact (hhead A hA).of_targetEquiv e

/-- An actual surjective quotient intertwiner from the decreasing induction to a
supplied segment socle, for use in product induction. -/
def IsSegmentSocle.decreasingHeadQuotient
    (hex : SegmentZelevinskyConstituentExistence.{uF,uV} F T)
    {Δ : Segment.{uV,uF} T}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSocle Δ π)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    letI := T.topology
    {q : (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation.IntertwiningMap
      π.representation // Function.Surjective q} := by
  letI := T.topology
  have h := hπ.isIrreducibleHead_down hex A hA
  exact ⟨h.2.choose, h.2.choose_spec.1⟩

end Langlands.PadicField.TopologicalData
