import Langlands.AllFieldBZ.Representation.Classification.SegmentSocleExistenceStatement
import Langlands.AllFieldBZ.Representation.Classification.RegularCuspidalProductSocleProof
import Langlands.AllFieldBZ.Representation.Derivative.OrderedCuspidalProductTwistOne

/-!
# Existence of the increasing-order segment socle

The members `ρ, νρ, …, ν^(m-1) ρ` of a segment have pairwise distinct cuspidal
data, so the unique-socle theorem `regularCuspidalProductSocle` for ordered
normalized products of distinct supercuspidal factors applies to the
increasing-order induction `segmentInduced`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.AllFieldBZ.Classification

open Langlands.GeneralLinear CategoryTheory
open LocalFieldPackage.TopologicalData

universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- A cuspidal datum fixed by the twist `ν^s` with a real exponent `s` has `s = 0`. -/
private theorem realTwist_eq_zero {ρ : CuspidalDatum.{uV, uF} T} {s : ℝ}
    (h : ρ.twist s = ρ) : s = 0 := by
  let := T.topology
  obtain ⟨r, hr, cls⟩ := ρ
  have hcls : T.supercuspidalClassRealPowerTwist r s cls = cls := by
    simpa only [CuspidalDatum.twist, CuspidalDatum.mk.injEq, heq_eq_eq, true_and] using h
  obtain ⟨A, rfl⟩ := Quotient.exists_rep cls
  let A' := SupercuspidalRep.twist (T.determinantPowerCharacter r s)
    (T.isOpen_ker_determinantPowerCharacter r s)
    (T.ker_determinant_le_ker_determinantPowerCharacter r s) A
  change A'.isoClass = A.isoClass at hcls
  obtain ⟨e⟩ := (SupercuspidalRep.isoClass_eq_iff A' A).mp hcls
  let e' := SmoothRep.equivOfIso ((supercuspidalProperty (F := F.Carrier)
    (n := r)).ι.mapIso e.symm)
  exact Derivative.OrderedCuspidalProductTwistOne.exponent_eq_zero T r hr A.obj
    A.property.2.1 A.property.1 s e'

/-- Distinct indices give distinct members `ν^i ρ` of a segment. -/
theorem segment_member_injective (Δ : Segment.{uV, uF} T) : Function.Injective Δ.member := by
  intro i j h
  have h' := congrArg (fun ρ : CuspidalDatum.{uV, uF} T => ρ.twist (-(j : ℝ))) h
  simp only [Segment.member, CuspidalDatum.twist_twist, neg_add_cancel,
    CuspidalDatum.twist_zero] at h'
  have hzero := realTwist_eq_zero T h'
  exact_mod_cast (neg_add_eq_zero.mp hzero).symm

/-- Every segment `Δ = [ρ, ν^(m-1) ρ]` has an irreducible smooth socle in the
increasing-order normalized induction `ρ × νρ × ⋯ × ν^(m-1) ρ`, and every
irreducible embedding into that induction has the same image. -/
theorem segmentSocleExistence : SegmentSocleExistenceStatement.{uF, uV} F T := by
  let := T.topology
  intro Δ
  obtain ⟨A, hA⟩ := Quotient.exists_rep Δ.base.cls
  have hrep : Δ.base.IsRepresentedBy A := hA
  let B := T.cuspidalShape (fun i : Fin Δ.length => Δ.member i)
    (n := Δ.degree) (by simp [Segment.member, Nat.mul_comm])
  have hclass (i : Fin Δ.length) :
      (⟨B.size i, B.positive i, (T.segmentFactor Δ A i).isoClass⟩ :
        CuspidalDatum.{uV, uF} T) = Δ.member i :=
    congrArg (CuspidalDatum.mk (B.size i) (B.positive i))
      (T.segmentFactor_isRepresentedBy Δ hrep i)
  have hinj : Function.Injective (fun i =>
      (⟨B.size i, B.positive i, (T.segmentFactor Δ A i).isoClass⟩ :
        CuspidalDatum.{uV, uF} T)) := by
    intro i j hij
    exact Fin.ext (segment_member_injective T Δ ((hclass i).symm.trans (hij.trans (hclass j))))
  have h := regularCuspidalProductSocle T Δ.degree Δ.degree_pos B (T.segmentFactor Δ A) hinj
  change Langlands.Classification.HasIrreducibleSocle (T.segmentInduced Δ A).representation at h
  obtain ⟨V, _, _, π, hπ⟩ := h
  obtain ⟨j, hj, _⟩ := hπ.2
  let P := SmoothRep.of π (isSmooth_of_injective j hj (T.segmentInduced Δ A).isSmooth)
  exact ⟨P, A, hrep, hπ⟩

end Langlands.AllFieldBZ.Classification
