import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof
import Langlands.Representation.Parabolic.NaturalFirstAdjointness

/-! Identification of supplied segment heads through decreasing induction. -/

noncomputable section

namespace Langlands.Classification

universe uG uV

variable {G : Type uG} [Group G]
  {V W W' : Type uV} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
  {ρ : Representation ℂ G V} {π : Representation ℂ G W}
  {π' : Representation ℂ G W'}

/-- Equivalence of the constituent preserves a strong socle and all of its
image uniqueness clauses. -/
theorem IsIrreducibleSocle.of_targetEquiv (h : IsIrreducibleSocle ρ π)
    (e : π.Equiv π') : IsIrreducibleSocle ρ π' := by
  obtain ⟨hπ, j, hj, hu⟩ := h
  refine ⟨(Weil.IsomorphismInvariance.irreducible_iff e).mp hπ,
    j.comp e.symm.toIntertwiningMap, hj.comp e.symm.injective, ?_⟩
  intro W'' _ _ σ hσ j' hj'
  rw [hu W'' σ hσ j' hj']
  exact (LinearMap.range_comp_of_range_eq_top j.toLinearMap
    (LinearMap.range_eq_top.mpr e.symm.surjective)).symm

/-- Every actual irreducible subrepresentation of a representation with a
strong socle is equivalent to that socle. -/
theorem IsIrreducibleSocle.nonempty_equiv_of_subrepresentation
    (h : IsIrreducibleSocle ρ π) (hπ' : π'.IsIrreducible)
    (j : π'.IntertwiningMap ρ) (hj : Function.Injective j) :
    Nonempty (π'.Equiv π) := by
  obtain ⟨e⟩ := h.nonempty_socleEquiv
  exact ⟨(socleEquivOfInjective j hj (h.socle_eq π' hπ' j hj)).trans e.symm⟩

end Langlands.Classification

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A supplied strong special head is the strong socle of each decreasing
induction representing the same segment. -/
theorem IsSegmentHead.isIrreducibleSocle_down
    {Δ : Segment.{uV,uF} T}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentHead Δ π)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    letI := T.topology
    IsIrreducibleSocle
      (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation
      π.representation := by
  let := T.topology
  obtain ⟨π₀, hπ₀, hsocle⟩ := segmentSpecialConstituentExistence F T Δ
  obtain ⟨e⟩ :=
    ((T.isSegmentHead_iff Δ π A hA).mp hπ).nonempty_headEquiv
  obtain ⟨e₀⟩ :=
    ((T.isSegmentHead_iff Δ π₀ A hA).mp hπ₀).nonempty_headEquiv
  exact (hsocle A hA).of_targetEquiv (e₀.symm.trans e)

/-- An actual injective intertwiner from a supplied special head into the
decreasing induction, retaining injectivity in its type. -/
def IsSegmentHead.decreasingSocleEmbedding
    {Δ : Segment.{uV,uF} T}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentHead Δ π)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    letI := T.topology
    {j : π.representation.IntertwiningMap
        (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation //
      Function.Injective j} := by
  let := T.topology
  have h := hπ.isIrreducibleSocle_down A hA
  exact ⟨h.2.choose, h.2.choose_spec.1⟩

/-- An irreducible subrepresentation of the decreasing induction is equivalent
to any supplied special head of the corresponding segment. -/
theorem IsSegmentHead.nonempty_equiv_of_down_subrepresentation
    {Δ : Segment.{uV,uF} T}
    {π τ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentHead Δ π)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A)
    (hτ : letI := T.topology; τ.IsIrreducible)
    (j : letI := T.topology
      τ.representation.IntertwiningMap
        (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation)
    (hj : Function.Injective j) :
    letI := T.topology
    Nonempty (τ.representation.Equiv π.representation) := by
  let := T.topology
  exact (hπ.isIrreducibleSocle_down A hA).nonempty_equiv_of_subrepresentation hτ j hj

/-- A nonzero map from the upper normalized Jacquet module of an irreducible
representation to the decreasing tensor identifies that representation with
the special head. -/
theorem IsSegmentHead.nonempty_equiv_of_down_jacquet_hom
    {Δ : Segment.{uV,uF} T}
    {π τ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentHead Δ π)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A)
    (hτ : letI := T.topology; τ.IsIrreducible)
    (f : letI := T.topology
      (T.normalizedJacquet (BlockShape.uniform Δ.length Δ.rank Δ.rank_pos)
        τ.representation).IntertwiningMap
      (FiniteTensor.externalSmoothObject
        (T.segmentFactorsDown A.obj Δ.length Δ.rank_pos)).representation)
    (hf : f ≠ 0) :
    letI := T.topology
    Nonempty (τ.representation.Equiv π.representation) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup Δ.degree
  let : τ.representation.IsIrreducible := hτ
  let E := Parabolic.FirstAdjointness.equiv T
    (BlockShape.uniform Δ.length Δ.rank Δ.rank_pos) τ.isSmooth
    (σ := (FiniteTensor.externalSmoothObject
      (T.segmentFactorsDown A.obj Δ.length Δ.rank_pos)).representation)
  let j := E.symm f
  have hj0 : j ≠ 0 := fun hj => hf (E.symm.map_eq_zero_iff.mp hj)
  have hj : Function.Injective j :=
    (Representation.IsIrreducible.injective_or_eq_zero j).resolve_right hj0
  exact hπ.nonempty_equiv_of_down_subrepresentation A hA hτ j hj

end Langlands.PadicField.TopologicalData
