import Langlands.Representation.Classification.TadicUnitaryStatement
import Langlands.Representation.Classification.SingletonSegmentSocle

/-!
# The length-one Speh comparison

Evaluation identifies the one-factor centered induction with the original
block. Every irreducible quotient of that irreducible source is isomorphic
to it.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Moving exact rank transport from the source to the target of an isomorphism. -/
private theorem rankTransport_iso_iff {a b : ℕ} (h : a = b)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)) :
    Nonempty ((h ▸ A) ≅ B) ↔ Nonempty (A ≅ (h.symm ▸ B)) := by
  cases h
  rfl

/-- A surjective intertwiner out of an irreducible smooth representation
onto an irreducible representation is an isomorphism. -/
private theorem nonempty_iso_of_irreducibleQuotient {n : ℕ}
    (A B : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hA : letI := T.topology
      Representation.IsIrreducible A.representation)
    (hq : letI := T.topology
      IsIrreducibleQuotient A.representation B.representation) :
    letI := T.topology
    Nonempty (A ≅ B) := by
  let := T.topology
  let := hA
  let := hq.1
  let : Nontrivial B :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) B.representation.asModule
  obtain ⟨q, hq⟩ := hq.2
  have hne : q ≠ 0 := by
    intro hz
    exact LinearMap.ne_zero_of_surjective hq (congrArg (fun f => f.toLinearMap) hz)
  exact ⟨SmoothRep.mkIso (q.ofBijective
    ⟨(Representation.IsIrreducible.injective_or_eq_zero q).resolve_right hne, hq⟩)⟩

namespace SpehDatum

/-- The centered decreasing induction with one factor is its original block,
with the exact equality of group ranks displayed. -/
def centeredInducedLengthOneIso (d : SpehDatum.{uF, uV} F T)
    (h1 : d.length = 1) (h : d.degree = d.rank) :
    letI := T.topology
    d.centeredInduced ≅ (h.symm ▸ d.delta) := by
  letI := T.topology
  let B := BlockShape.uniform d.length d.rank d.rank_pos
  let i0 : Fin B.length := ⟨0, d.length_pos⟩
  let τ := fun i => (T.segmentFactor d.delta (d.exponent i)).representation
  let e := T.singleBlockNormalizedProductEquiv B h1 τ
    (fun i => (T.segmentFactor d.delta (d.exponent i)).isSmooth) i0
  have hzero : d.exponent i0 = 0 := by
    simp [SpehDatum.exponent, h1, i0]
  have hτ : τ i0 = d.delta.representation := by
    change realPowerTwist (T.determinantNorm d.rank) (d.exponent i0)
      d.delta.representation = _
    rw [hzero, realPowerTwist_zero]
  let eτ := equivOfRepresentationEq hτ
  refine SmoothRep.mkIso (e.trans ?_)
  refine (Representation.Equiv.mk eτ.toLinearEquiv ?_).trans
    (T.castRankEquiv h.symm d.delta)
  intro g
  exact eτ.isIntertwining' _

end SpehDatum

/-- A length-one Speh representation is exactly its discrete-series block. -/
theorem spehLengthOneComparison :
    SpehLengthOneComparison.{uF, uV} F T := by
  let := T.topology
  intro d h π h1 hd
  rw [rankTransport_iso_iff F T h π d.delta]
  let D := T.castRank h.symm d.delta
  let E : d.centeredInduced ≅ D := d.centeredInducedLengthOneIso F T h1 h
  have hD : Representation.IsIrreducible D.representation :=
    T.isIrreducible_castRank h.symm d.delta hd.1
  have hC : Representation.IsIrreducible d.centeredInduced.representation :=
    (Weil.IsomorphismInvariance.irreducible_iff (SmoothRep.equivOfIso E)).mpr hD
  constructor
  · intro hs
    obtain ⟨e⟩ := nonempty_iso_of_irreducibleQuotient F T _ _ hC hs.2.1
    exact ⟨e.symm ≪≫ E⟩
  · rintro ⟨e⟩
    let Q : d.centeredInduced ≅ π := E ≪≫ e.symm
    have hπ : Representation.IsIrreducible π.representation :=
      (Weil.IsomorphismInvariance.irreducible_iff (SmoothRep.equivOfIso Q)).mp hC
    refine ⟨hd, ⟨hπ, (SmoothRep.equivOfIso Q).toIntertwiningMap,
      (SmoothRep.equivOfIso Q).surjective⟩, ?_⟩
    intro π' hq
    obtain ⟨e'⟩ := nonempty_iso_of_irreducibleQuotient F T _ _ hC hq
    exact ⟨e'.symm ≪≫ Q⟩

end Langlands.Classification
