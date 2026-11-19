import Langlands.LocalFactor.Ramification.Herbrand.KummerTruncationProof
import Langlands.LocalFactor.Ramification.Herbrand.KummerStepUpperSupProof

/-!
# The relative inverse Herbrand function of a Kummer step

Transitivity at the Kummer break gives the identity branch. Above the break,
the upper groups fix the radical field, so the slope is its relative
ramification index. Continuity extends the increment formula to the break.
-/

noncomputable section

namespace Langlands.Ramification.Kummer

open _root_.Langlands.Ramification.HerbrandBridge

universe u

/-- The relative inverse Herbrand function of the uniformizer radical step
has slope one through the Kummer break and slope `p` above it. -/
theorem kummerStepHerbrandPsi : KummerStepHerbrandPsiStatement.{u} := by
  intro p hp F ϖ α hϖ hα
  let E := adjoinFiniteIntermediate F α
  let b := kummerBreak F
  have hb : 0 < b := kummerBreak_pos F
  have hb₁ : (-1 : ℝ) ≤ b := by linarith
  have hidentity : ∀ x : ℝ, -1 ≤ x → x ≤ b → relativeHerbrandPsi E x = x :=
    herbrandPsiTruncation p F E b (kummerStepUpperSup p F ϖ α hϖ hα b hb₁ le_rfl)
  refine ⟨hidentity, ?_⟩
  have hindex : E.field.fixingSubgroup.relIndex (F.absoluteInertia F.canonicalTopologicalData) =
      p := by
    apply Nat.eq_of_mul_eq_mul_right F.canonicalTopologicalData.ramificationIndex_pos
    exact (fixingSubgroup_relIndex_absoluteInertia_mul F E).trans
      (kummerStep_root_ord_and_ramificationIndex F hϖ hα).2
  intro x hx
  change b ≤ x at hx
  have hincrements : Set.EqOn
      (fun y => relativeHerbrandPsi E (y + (x - b)) - relativeHerbrandPsi E y)
      (fun _ => (p : ℝ) * (x - b)) (Set.Ioi b) := by
    intro y hy
    have hby : b < y := hy
    have hle : y ≤ y + (x - b) := le_add_of_nonneg_right (sub_nonneg.mpr hx)
    have h := relativeHerbrandPsi_sub_eq_relIndex E (hb.le.trans hby.le)
      (kummerStep_upper_le_fixingSubgroup F hϖ hα hby) le_rfl hle
    rw [hindex] at h
    simpa only [add_sub_cancel_left] using h
  have hcontinuous : Continuous
      (fun y => relativeHerbrandPsi E (y + (x - b)) - relativeHerbrandPsi E y) :=
    ((relativeHerbrandPsi_continuous E).comp (continuous_id.add continuous_const)).sub
      (relativeHerbrandPsi_continuous E)
  have hclosed := hincrements.closure hcontinuous continuous_const
  rw [closure_Ioi] at hclosed
  have hstep :
      relativeHerbrandPsi E (b + (x - b)) - relativeHerbrandPsi E b =
        (p : ℝ) * (x - b) :=
    hclosed (Set.mem_Ici.mpr le_rfl)
  rw [show b + (x - b) = x by ring, hidentity b hb₁ le_rfl] at hstep
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hbreak : b * ((p : ℝ) - 1) =
      (p : ℝ) * (F.canonicalTopologicalData.ramificationIndex : ℝ) :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hp₁.ne')
  change relativeHerbrandPsi E x =
    (p : ℝ) * x - (p : ℝ) * (F.canonicalTopologicalData.ramificationIndex : ℝ)
  linear_combination hstep - hbreak

end Langlands.Ramification.Kummer
