import Langlands.Group.GL.LowerTriangularBigCellConull
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Group.GL.MirabolicTailConullProof
/-!
# The lower big cell `N · B⁻` is conull

For an invertible matrix `g`, write `A_k(g)` for the matrix agreeing with `g`
on the rows and columns of index at least `k` and with the identity elsewhere,
so that `det A_k(g)` is the bottom-right minor of size `m - k`. Then `g = u b`
with `u` upper unipotent and `b` invertible lower triangular exactly when all
these minors are nonzero. The complement of `N · B⁻` is closed and null for
every left Haar measure: it is covered by finitely many pieces, each moved off
itself by an elementary transvection with a small nonzero parameter. A
compatible quotient measure on `N \ G` vanishes on every measurable set whose
preimage is Haar-null, so the cosets not represented by `B⁻` form a null set.
-/

namespace Langlands.AllField.GeneralLinear
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero padic_lowerTriangular_leftQuotient_conull padic_setOf_not_upperUnipotent_mul_lowerTriangular
open Langlands.AllField.GeneralLinear

open _root_.MeasureTheory Filter _root_.Topology Set Matrix

universe uF

section Corner


end Corner

section Null



end Null

end Langlands.AllField.GeneralLinear

namespace Langlands.AllField.QuotientIntegration
open Langlands.QuotientIntegration
open Langlands.AllField.QuotientIntegration

open _root_.MeasureTheory Set

end Langlands.AllField.QuotientIntegration

namespace Langlands.AllField.GeneralLinear
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero padic_lowerTriangular_leftQuotient_conull padic_setOf_not_upperUnipotent_mul_lowerTriangular
open Langlands.AllField.GeneralLinear

open _root_.MeasureTheory Filter _root_.Topology Set
open Langlands.QuotientIntegration
open Langlands.AllField.QuotientIntegration

section Padic

variable {F : Type uF} [Field F]

/-- In the supplied topology, the complement of `N · B⁻` in `GL_m(F)` is closed
and null for every left Haar measure. -/
theorem padic_setOf_not_upperUnipotent_mul_lowerTriangular (T : LocalFieldData F) (m : ℕ) :
    letI := T.topology
    letI := borel (GeneralLinear m F)
    IsClosed {g : GeneralLinear m F | ¬ ∃ u ∈ upperUnipotent m F,
        ∃ b ∈ lowerTriangularSubgroup m F, u * b = g} ∧
      ∀ μ : Measure (GeneralLinear m F), μ.IsHaarMeasure →
        μ {g : GeneralLinear m F | ¬ ∃ u ∈ upperUnipotent m F,
          ∃ b ∈ lowerTriangularSubgroup m F, u * b = g} = 0 := by
  let := T.topology
  let mG : MeasurableSpace (GeneralLinear m F) := borel _
  have : BorelSpace (GeneralLinear m F) := ⟨rfl⟩
  have := T.fieldT2
  have := T.generalLinearTopologicalGroup m
  have := T.generalLinearLocallyCompactSpace m
  have := T.generalLinearSecondCountableTopology m
  have : IsTopologicalRing F := by
    let := T.valuativeRel
    have := T.localField
    infer_instance
  refine ⟨isClosed_setOf_not_upperUnipotent_mul_lowerTriangular, fun μ hμ => ?_⟩
  have := hμ
  have : μ.InnerRegular := inferInstance
  exact haar_setOf_not_upperUnipotent_mul_lowerTriangular
    (padic_exists_ne_zero_mem_nhds_zero T) μ

set_option linter.overlappingInstances false in
/-- For every compatible quotient measure on `N_m \ GL_m(F)`, in the supplied
topology, the cosets with no representative in `B⁻` form a null set. -/
theorem padic_lowerTriangular_leftQuotient_conull (T : LocalFieldData F) (m : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (GeneralLinear m F)
    letI : BorelSpace (GeneralLinear m F) := ⟨rfl⟩
    letI := borel (upperUnipotent m F)
    letI : BorelSpace (upperUnipotent m F) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent m F))
    letI : BorelSpace (LeftQuotient (upperUnipotent m F)) := ⟨rfl⟩
    ∀ (μG : Measure (GeneralLinear m F)) (μH : Measure (upperUnipotent m F))
      [μG.IsHaarMeasure] [μG.Regular] [μH.IsHaarMeasure] [μH.Regular]
      [μH.IsMulRightInvariant] (μ : Measure (LeftQuotient (upperUnipotent m F))),
      IsCompatible (upperUnipotent m F) μG μH μ →
      μ {q | ∀ b ∈ lowerTriangularSubgroup m F,
        (Quotient.mk _ b : LeftQuotient (upperUnipotent m F)) ≠ q} = 0 := by
  intro μG μH _ _ _ _ _ μ hμ
  let := T.topology
  let mG : MeasurableSpace (GeneralLinear m F) := borel _
  have : BorelSpace (GeneralLinear m F) := ⟨rfl⟩
  let mN : MeasurableSpace (upperUnipotent m F) := borel _
  have : BorelSpace (upperUnipotent m F) := ⟨rfl⟩
  let mQ : MeasurableSpace (LeftQuotient (upperUnipotent m F)) := borel _
  have : BorelSpace (LeftQuotient (upperUnipotent m F)) := ⟨rfl⟩
  have := T.fieldT2
  have := T.generalLinearTopologicalGroup m
  have := T.generalLinearLocallyCompactSpace m
  have := T.generalLinearSecondCountableTopology m
  let N := upperUnipotent m F
  have hpre : leftQuotientMap N ⁻¹'
      {q | ∀ b ∈ lowerTriangularSubgroup m F, (Quotient.mk _ b : LeftQuotient N) ≠ q} =
      {g : GeneralLinear m F |
        ¬ ∃ u ∈ N, ∃ b ∈ lowerTriangularSubgroup m F, u * b = g} := by
    ext g
    simp only [mem_preimage, mem_ofPred_eq, leftQuotientMap_apply]
    constructor
    · rintro h ⟨u, hu, b, hb, rfl⟩
      refine h b hb (Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_))
      rw [mul_inv_cancel_right]
      exact hu
    · intro h b hb hbg
      have hrel := QuotientGroup.rightRel_apply.mp (Quotient.exact hbg)
      exact h ⟨g * b⁻¹, hrel, b, hb, inv_mul_cancel_right g b⟩
  have hnull := (padic_setOf_not_upperUnipotent_mul_lowerTriangular T m).2 μG inferInstance
  have hclosed := (padic_setOf_not_upperUnipotent_mul_lowerTriangular T m).1
  have hS : IsClosed
      {q | ∀ b ∈ lowerTriangularSubgroup m F, (Quotient.mk _ b : LeftQuotient N) ≠ q} := by
    rw [← (leftQuotient_isOpenQuotientMap N).isQuotientMap.isCoinducing.isClosed_preimage, hpre]
    exact hclosed
  obtain ⟨K, hKc, -⟩ := T.generalLinearCompactOpen m univ univ_mem
  refine IsCompatible.measure_eq_zero_of_preimage UpperUnipotent.isClosed K hKc hμ
    hS.measurableSet ?_
  rw [hpre]
  exact hnull

end Padic

end Langlands.AllField.GeneralLinear
