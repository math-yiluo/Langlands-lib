import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupport
import Langlands.AllFieldBZ.Representation.Classification.IrreducibleProductFiniteLengthProof

/-!
# Ordered inductions attached to a Zelevinsky segment

The two orders of the determinant twists give the ambient representations for
the segment socle and the special head over an arbitrary nonarchimedean local field.
-/

noncomputable section

open CategoryTheory

namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData

universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

namespace Segment

variable {T}

/-- The rank of the group carrying the normalized product of the segment members. -/
abbrev degree (Δ : Segment.{uV, uF} T) : ℕ := Δ.length * Δ.rank

theorem degree_pos (Δ : Segment.{uV, uF} T) : 0 < Δ.degree :=
  Nat.mul_pos Δ.length_pos Δ.rank_pos

end Segment

/-- The actual twist `ν^i A` of a representative of the beginning of the segment. -/
def segmentFactor (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (i : Fin Δ.length) :
    letI := T.topology
    GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (Δ.member i).rank) :=
  letI := T.topology
  GeneralLinear.SupercuspidalRep.twist
    (T.determinantPowerCharacter Δ.rank ((i : ℕ) : ℝ))
    (T.isOpen_ker_determinantPowerCharacter Δ.rank ((i : ℕ) : ℝ))
    (T.ker_determinant_le_ker_determinantPowerCharacter Δ.rank ((i : ℕ) : ℝ)) A

theorem segmentFactor_isRepresentedBy (Δ : Segment.{uV, uF} T)
    {A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)}
    (hA : Δ.base.IsRepresentedBy A) (i : Fin Δ.length) :
    (Δ.member i).IsRepresentedBy (T.segmentFactor Δ A i) :=
  congrArg (T.supercuspidalClassRealPowerTwist Δ.rank ((i : ℕ) : ℝ)) hA

/-- Normalized upper-block induction `A × ν A × ⋯ × ν^(m-1) A`. -/
def segmentInduced (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier) :=
  T.cuspidalProductInduced (fun i : Fin Δ.length => Δ.member i)
    (by simp [Segment.member, Nat.mul_comm]) (T.segmentFactor Δ A)

/-- Normalized upper-block induction `ν^(m-1) A × ⋯ × ν A × A`. -/
def segmentInducedDown (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier) :=
  T.cuspidalProductInduced (fun i : Fin Δ.length => Δ.member i.rev)
    (by simp [Segment.member, Nat.mul_comm]) (fun i => T.segmentFactor Δ A i.rev)

/-- Increasing-order induction is independent of the representative of the beginning. -/
def segmentInducedIsoOfRepresented (Δ : Segment.{uV, uF} T)
    {A A' : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)}
    (hA : Δ.base.IsRepresentedBy A) (hA' : Δ.base.IsRepresentedBy A') :
    T.segmentInduced Δ A ≅ T.segmentInduced Δ A' :=
  T.cuspidalProductInducedIsoOfRepresented _
    (T.segmentFactor_isRepresentedBy Δ hA) (T.segmentFactor_isRepresentedBy Δ hA')

/-- Decreasing-order induction is independent of the representative of the beginning. -/
def segmentInducedDownIsoOfRepresented (Δ : Segment.{uV, uF} T)
    {A A' : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)}
    (hA : Δ.base.IsRepresentedBy A) (hA' : Δ.base.IsRepresentedBy A') :
    T.segmentInducedDown Δ A ≅ T.segmentInducedDown Δ A' :=
  T.cuspidalProductInducedIsoOfRepresented _
    (fun i => T.segmentFactor_isRepresentedBy Δ hA i.rev)
    (fun i => T.segmentFactor_isRepresentedBy Δ hA' i.rev)

theorem segmentInduced_finiteLength (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)) :
    letI := T.topology
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear Δ.degree F.Carrier))
      (T.segmentInduced Δ A).representation.asModule := by
  let := T.topology
  apply Classification.irreducibleProductFiniteLength F T Δ.degree Δ.degree_pos
  exact fun i => (T.segmentFactor Δ A i).property.1

theorem segmentInducedDown_finiteLength (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)) :
    letI := T.topology
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear Δ.degree F.Carrier))
      (T.segmentInducedDown Δ A).representation.asModule := by
  let := T.topology
  apply Classification.irreducibleProductFiniteLength F T Δ.degree Δ.degree_pos
  exact fun i => (T.segmentFactor Δ A i.rev).property.1

/-- The irreducible socle relation in the increasing-order induced representation. -/
def IsSegmentSocle (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)) : Prop :=
  letI := T.topology
  ∃ A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank),
    Δ.base.IsRepresentedBy A ∧
      Langlands.Classification.IsIrreducibleSocle
        (T.segmentInduced Δ A).representation π.representation

/-- The irreducible head relation in the increasing-order induced representation. -/
def IsSegmentHead (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)) : Prop :=
  letI := T.topology
  ∃ A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank),
    Δ.base.IsRepresentedBy A ∧
      Langlands.Classification.IsIrreducibleHead
        (T.segmentInduced Δ A).representation π.representation

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
