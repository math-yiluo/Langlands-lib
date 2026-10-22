import Langlands.Group.GL.TriangularParabolic
import Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
import Langlands.Representation.Whittaker.Iwasawa

noncomputable section

namespace Langlands.Parabolic

open Langlands.GeneralLinear

universe uF

section Local

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The integral group of every rank, including rank zero, is compact for the
supplied topology. -/
theorem isCompact_integralRange (m : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    IsCompact (Iwasawa.integralRange (ValuativeRel.valuation F.Carrier) m :
      Set (Langlands.GeneralLinear m F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  cases m with
  | zero =>
    refine Set.Subsingleton.isCompact fun x _ y _ => ?_
    exact Units.ext (Matrix.ext fun i _ => i.elim0)
  | succ m =>
    have hK := Conductor.isCompact_levelOpenSubgroup F.Carrier m 0
    have heq : (Conductor.levelOpenSubgroup F.Carrier m 0 :
        Set (Langlands.GeneralLinear (m + 1) F.Carrier)) =
          Iwasawa.integralRange (ValuativeRel.valuation F.Carrier) (m + 1) := by
      rw [Iwasawa.integralRange_succ]
      change (Conductor.levelSubgroup F.Carrier m 0 :
        Set (Langlands.GeneralLinear (m + 1) F.Carrier)) = _
      rw [Conductor.levelSubgroup_zero]
    rw [← heq]
    exact hK

/-- Every right coset `P * g` of the actual block parabolic meets the integral group. -/
theorem quotientMap_image_integralRange {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.valuativeRel
    Induction.quotientMap (B.parabolic F.Carrier) ''
      (Iwasawa.integralRange (ValuativeRel.valuation F.Carrier) n :
        Set (Langlands.GeneralLinear n F.Carrier)) = Set.univ := by
  let := T.valuativeRel
  refine Set.eq_univ_of_forall fun x => ?_
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨k, hk, hup⟩ :=
      Iwasawa.exists_mul_upperTriangular (ValuativeRel.valuation F.Carrier) n g
    refine ⟨k⁻¹, inv_mem hk, Quotient.sound ?_⟩
    change QuotientGroup.rightRel _ k⁻¹ g
    rw [QuotientGroup.rightRel_apply, inv_inv]
    exact B.mem_parabolic_of_isUpperTriangular _ hup

end Local

/-- The actual quotient `P \ G` of `GL_n(F)` by a standard block parabolic is compact,
for the supplied topology, every block shape and every rank including zero. -/
theorem parabolicQuotientCompact {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    ParabolicQuotientCompactClause F T B := by
  let := T.topology
  let := T.valuativeRel
  unfold ParabolicQuotientCompactClause
  refine ⟨?_⟩
  rw [← quotientMap_image_integralRange T B]
  exact (isCompact_integralRange T n).image continuous_quotient_mk'

end Langlands.Parabolic
