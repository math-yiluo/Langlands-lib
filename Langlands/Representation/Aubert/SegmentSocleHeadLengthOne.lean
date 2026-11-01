import Langlands.Representation.Aubert.SegmentSocleHeadBoundary
import Langlands.Representation.Aubert.SegmentSocleHeadStatement
import Langlands.Group.GL.RankReindex
import Langlands.Representation.Filtration.CentralEigenspaceSplitting

/-! The actual single-factor segment induction and its Aubert exchange. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open GeneralLinear SmoothRep

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The actual length-one segment induction is its single factor, with the
necessary equality-of-rank transport displayed explicitly. -/
def segmentInducedOneEquiv {r : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (hr : 0 < r) :
    letI := T.topology
    (T.segmentInduced A 1 hr).representation.Equiv
      (A.representation.comp
        (GeneralLinear.reindex (R := F.Carrier) (finCongr (by omega : r = 1 * r))).symm.toMonoidHom) := by
  let := T.topology
  let B := BlockShape.uniform 1 r hr
  have e := T.singleBlockNormalizedProductEquiv B rfl
    (fun i => (T.segmentFactors A 1 hr i).representation)
    (fun i => (T.segmentFactors A 1 hr i).isSmooth) ⟨0, by change 0 < 1; omega⟩
  refine e.trans (Langlands.equivOfRepresentationEq ?_)
  dsimp only [segmentFactors, segmentFactor, SmoothRep.twist, SmoothRep.of,
    SmoothRep.representation]
  simp only [determinantPowerCharacter, Nat.cast_zero, realPowerCharacter_zero,
    Langlands.twist_one]
  rfl

private theorem rankTransport_supercuspidal {r n : ℕ} (h : r = n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
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

private theorem rankTransport_irreducible {r n : ℕ} (h : r = n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear r F.Carrier) V)
    (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible (ρ.comp
      (GeneralLinear.reindex (R := F.Carrier) (finCongr h)).symm.toMonoidHom) := by
  subst n
  rw [GeneralLinear.reindex_finCongr_rfl]
  change Representation.IsIrreducible (ρ.comp (MonoidHom.id _))
  simpa only [MonoidHom.comp_id] using hρ

/-- A single-factor supercuspidal segment induction is irreducible and
supercuspidal, without a classification or constituent-existence input. -/
theorem segmentInducedOne_supercuspidal {r : ℕ}
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) (hr : 0 < r) :
    letI := T.topology
    (T.segmentInduced A.obj 1 hr).IsIrreducible ∧
      IsSupercuspidal (T.segmentInduced A.obj 1 hr).representation := by
  let := T.topology
  let e := T.segmentInducedOneEquiv A.obj hr
  constructor
  · exact (Langlands.isIrreducible_iff_of_equiv e).mpr
      (rankTransport_irreducible _ A.obj.representation A.property.1)
  · exact GeneralLinear.isSupercuspidal_of_equiv e.symm
      (rankTransport_supercuspidal T _ A.obj.representation A.property.2)

/-- For a length-one segment the actual strong socle and head are equivalent,
and that socle is supercuspidal. The maps come from the supplied relations. -/
theorem segmentConstituents_length_one
    (Δ : T.Segment.{max uF uV, uF}) (hΔ : Δ.length = 1)
    (πZ πS : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hZ : T.IsSegmentSocle Δ πZ) (hS : T.IsSegmentHead Δ πS) :
    letI := T.topology
    Nonempty (πZ.representation.Equiv πS.representation) ∧
      IsSupercuspidal πZ.representation := by
  let := T.topology
  obtain ⟨A, hA, hZirr, j, hj, _⟩ := hZ
  obtain ⟨hSirr, q, hq, _⟩ := (T.isSegmentHead_iff Δ πS A hA).mp hS
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
  have hj0 : j ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := CentralEigenspaceSplitting.exists_ne_zero_of_isIrreducible hZirr
    apply hv
    apply hj
    rw [hz]
    rfl
  have hq0 : q ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := CentralEigenspaceSplitting.exists_ne_zero_of_isIrreducible hSirr
    obtain ⟨w, hw⟩ := hq v
    apply hv
    rw [← hw, hz]
    rfl
  have hjs := (Representation.IsIrreducible.surjective_or_eq_zero j).resolve_right hj0
  have hqi := (Representation.IsIrreducible.injective_or_eq_zero q).resolve_right hq0
  let eZ := j.ofBijective ⟨hj, hjs⟩
  let eS := q.ofBijective ⟨hqi, hq⟩
  exact ⟨⟨eZ.trans eS⟩, GeneralLinear.isSupercuspidal_of_equiv eZ.symm hI.2⟩

end Langlands.PadicField.TopologicalData

namespace Langlands.Aubert

open GeneralLinear SmoothRep

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual signed segment exchange restricted to segments of length one.
It asserts no existence of the supplied strong constituents. -/
def LengthOneSegmentSocleHeadStatement : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{max uF uV, uF}), Δ.length = 1 →
    ∀ (πZ πS : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
      (hZ : T.IsSegmentSocle Δ πZ) (hS : T.IsSegmentHead Δ πS),
      let x := GeneralLinear.finiteLengthClass Δ.degree F.Carrier πZ
        (SmoothRep.hasFiniteLength_of_isIrreducible (by
          obtain ⟨_, _, h⟩ := hZ
          exact h.1))
      let y := GeneralLinear.finiteLengthClass Δ.degree F.Carrier πS
        (SmoothRep.hasFiniteLength_of_isIrreducible (by
          obtain ⟨_, _, h⟩ := hS
          exact h.1))
      alternatingOperator.{uF, uV} F T Δ.degree x =
        (-1 : ℤ) ^ (Δ.degree - Δ.length) • y

/-- The length-one actual segment exchange follows from the supercuspidal
eigenvalue and the actual constituent equivalence. -/
theorem lengthOneSegmentSocleHead : LengthOneSegmentSocleHeadStatement.{uF, uV} F T := by
  let := T.topology
  intro Δ hΔ πZ πS hZ hS
  obtain ⟨⟨e⟩, hsc⟩ := T.segmentConstituents_length_one Δ hΔ πZ πS hZ hS
  dsimp only
  rw [alternatingOperator_supercuspidal F T Δ.degree_pos πZ _ hsc]
  have hc := SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv
    (SmoothRep.hasFiniteLength_of_isIrreducible (by obtain ⟨_, _, h⟩ := hZ; exact h.1))
    (SmoothRep.hasFiniteLength_of_isIrreducible (by obtain ⟨_, _, h⟩ := hS; exact h.1)) e
  change GeneralLinear.finiteLengthClass Δ.degree F.Carrier πZ _ =
    GeneralLinear.finiteLengthClass Δ.degree F.Carrier πS _ at hc
  rw [hc]
  have hs : (-1 : ℤ) ^ (Δ.degree - 1) = (-1 : ℤ) ^ (Δ.degree - Δ.length) := by
    rw [hΔ]
  exact congrArg (fun z : ℤ => z •
    GeneralLinear.finiteLengthClass Δ.degree F.Carrier πS _) hs

end Langlands.Aubert
