import Langlands.Representation.Archimedean.RealRankFourCasimir
import Langlands.Representation.Archimedean.RealRankFourEnergy
import Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionReduction
import Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement

/-!
# The unitary bound on an opposite pair of real discrete blocks

An invariant positive form turns the compact highest vector and trace-free
Casimir computation into the weak bound. An unlinked pair excludes equality.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean
open RealRankFourCompact RealRankFourMatrices
open scoped InnerProductSpace TensorProduct Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem realRankFour_abs_le_half {d e : ComplexCharacterData}
    (hweight : d.weight.natAbs = e.weight.natAbs) (u : ℂ) (a : ℝ)
    (hd : d.exponent = u + (a : ℂ)) (he : e.exponent = u - (a : ℂ))
    (hunit : IsRealUnitarizableGKModule 4 (realStandardRep 4 (pair d e))
      (realStandardLie 4 (pair d e))) :
    |a| ≤ 1 / 2 := by
  obtain ⟨b, hb⟩ := hunit
  let _ : InnerProductSpace.Core ℂ (Standard d e) := b.toInnerProductCore
  let _ : NormedAddCommGroup (Standard d e) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let _ : InnerProductSpace ℂ (Standard d e) :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (Standard d e))
  obtain ⟨v, hv, hraise, hleft, hright⟩ := exists_highest_vector d e hweight
  have hv0 : v ≠ 0 := by
    intro h
    exact hv (by rw [h]; rfl)
  have hskew (ij : Fin 4 × Fin 4) (x y : Standard d e) :
      ⟪action d e (basisC ij) x, y⟫_ℂ = -⟪x, action d e (basisC ij) y⟫_ℂ := by
    rw [← castMatrix_basisR ij, action_castMatrix]
    exact eq_neg_of_add_eq_zero_left (hb (basisR ij) x y)
  let m : ℝ := (d.weight.natAbs : ℝ) + 1
  have hm : 0 < m := by
    dsimp [m]
    positivity
  refine RealRankFourEnergy.abs_le_half (action d e) hskew m a hm v hv0 hraise ?_ hright ?_
  · simpa only [m, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one] using hleft
  · simpa only [m, add_sub_cancel_right] using
      RealRankFourCasimir.traceFreeCasimir v hv hweight u a hd he v

/-- The strict unitary bound for two unlinked real discrete blocks of equal absolute
weight with exponents `u + a` and `u - a`. -/
def RealRankFourUnitaryBoundStatement : Prop :=
  ∀ (d e : ComplexCharacterData), d.weight ≠ 0 → d.weight.natAbs = e.weight.natAbs →
    ∀ (u : ℂ) (a : ℝ), d.exponent = u + (a : ℂ) → e.exponent = u - (a : ℂ) →
      AreRealBlocksUnlinked (.induced d) (.induced e) →
      IsRealUnitarizableGKModule 4 (realStandardRep 4 (pair d e))
        (realStandardLie 4 (pair d e)) →
      |a| < 1 / 2

theorem realRankFourUnitaryBound : RealRankFourUnitaryBoundStatement := by
  intro d e hd0 hweight u a hd he hunlinked hunit
  have he0 : e.weight ≠ 0 := by
    intro h
    exact hd0 (Int.natAbs_eq_zero.mp (hweight.trans (by simp [h])))
  have hle := realRankFour_abs_le_half hweight u a hd he hunit
  by_contra! h
  have habs : |a| = 1 / 2 := le_antisymm hle h
  have hnotLinked := hunlinked (.discrete d.weight.natAbs d.exponent)
    (by simp [realBlockMoeglinData, hd0]) (.discrete e.weight.natAbs e.exponent)
    (by simp [realBlockMoeglinData, he0])
  apply hnotLinked
  refine ⟨1, Nat.one_pos, ?_⟩
  simp only [← hweight, sub_self, Int.natAbs_zero, Nat.cast_zero, zero_div, zero_add, Nat.cast_one]
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha] at habs
    left
    rw [hd, he, habs]
    push_cast
    ring
  · rw [abs_of_neg ha, neg_eq_iff_eq_neg] at habs
    right
    rw [hd, he, habs]
    push_cast
    ring

end Langlands.Archimedean
