import Langlands.Representation.Classification.CenteredUnitarySegmentFamily
import Langlands.Representation.Classification.SegmentHeadContragredient
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrableSemisimplicity

/-! # Actual duals of centered unitary segment parameters -/

noncomputable section

namespace Langlands.PadicField.TopologicalData.Segment

open Classification.CuspidalProductContragredient

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The midpoint base of the reversed dual segment is the dual of the
original midpoint base. -/
theorem dual_midpoint_base (Δ : T.Segment.{uV, uF}) :
    (Δ.dual.twist (((Δ.length : ℝ) - 1) / 2)).base =
      dualDatum (Δ.twist (((Δ.length : ℝ) - 1) / 2)).base := by
  have hlen : ((Δ.length - 1 : ℕ) : ℝ) = (Δ.length : ℝ) - 1 :=
    by
      rw [Nat.cast_sub (by have := Δ.length_pos; omega : 1 ≤ Δ.length)]
      norm_num
  simp only [twist, dual, last, member, dualDatum_twist, CuspidalDatum.twist_twist]
  congr 1
  rw [hlen]
  ring

end Langlands.PadicField.TopologicalData.Segment

namespace Langlands.Classification

open GeneralLinear CuspidalProductContragredient

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem represents_transport
    {ρ ρ' : T.CuspidalDatum.{max uF uV, uF}} (h : ρ = ρ')
    (A : letI := T.topology
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) :
    ρ'.IsRepresentedBy ((congrArg PadicField.TopologicalData.CuspidalDatum.rank h) ▸ A) := by
  cases h
  exact hA

private theorem contragredient_transport {a n : ℕ} (h : a = n)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) :
    (letI := T.topology; letI := T.generalLinearTopologicalGroup a
      (h.symm ▸ π).contragredient) =
    (h.symm ▸ (letI := T.topology; letI := T.generalLinearTopologicalGroup n
      π.contragredient)) := by
  cases h
  rfl

/-- Retain the actual smooth dual of the supplied action, reverse the segment,
and choose the actual smooth dual of the supplied midpoint base. -/
def SquareIntegrableSegmentParameter.contragredient
    {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (d : SquareIntegrableSegmentParameter F T n π) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    SquareIntegrableSegmentParameter F T n π.contragredient := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  refine
    { segment := d.segment.dual
      degree_eq := d.degree_eq
      base := dualRep T d.base
      base_repr := ?_
      unitarizable := ?_
      head := ?_ }
  · change
      (d.segment.dual.twist (((d.segment.length : ℝ) - 1) / 2)).base.IsRepresentedBy
        (dualRep T d.base)
    exact represents_transport F T
      (PadicField.TopologicalData.Segment.dual_midpoint_base d.segment).symm
      (dualRep T d.base) (dualRep_represents d.base_repr)
  · let := T.generalLinearTopologicalGroup d.segment.rank
    change IsUnitarizable (smoothContragredient d.base.obj.representation)
    exact HarishChandraSchwartz.isUnitarizable_smoothContragredient_of_admissible
      (compactOpen_cofinal F T d.segment.rank) d.base.property.2.1 d.unitarizable
  · have hc := d.head.contragredient
    rw [contragredient_transport F T d.degree_eq π] at hc
    exact hc

@[simp]
theorem SquareIntegrableSegmentParameter.contragredient_segment
    {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (d : SquareIntegrableSegmentParameter F T n π) :
    (d.contragredient F T).segment = d.segment.dual := rfl

@[simp]
theorem SquareIntegrableSegmentParameter.contragredient_base
    {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (d : SquareIntegrableSegmentParameter F T n π) :
    (d.contragredient F T).base = dualRep T d.base := rfl

end Langlands.Classification
