import Langlands.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof
import Langlands.AllField.Representation.CuspidalSupport.CompactCoefficientFinitenessProof
import Langlands.AllField.Representation.CuspidalSupport.HarishChandraAssembly
import Langlands.AllField.Representation.CuspidalSupport.LeviCompactPart
/-! Quasicuspidal decomposition of arbitrary smooth product-Levi representations. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding CompactCoefficientFixedLevelFinitenessTheorem DeterminantUnitCornerStructureStatement DeterminantUnitSmoothDualStatement LeviHarishChandraConverseTheorem LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem LeviQuasicuspidalDecompositionTheorem compactCoefficientFixedLevelFiniteness compactCoefficientFixedLevelFiniteness_of_cornerStructure continuous_determinantUnitInclusion determinantUnitCompactOpenCofinal determinantUnitCornerStructure determinantUnitInclusion determinantUnitInclusion_apply determinantUnitIsotypic_isCompl determinantUnitLocallyCompactSpace determinantUnitNonarchimedean determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal determinantUnitTotalIsotypic_compact determinantUnitTotalIsotypic_exhaust exists_leviPiOpenSubgroup_subset isCompact_leviPiOpenSubgroup isOpen_determinantUnitSubgroup isSmooth_determinantUnitRestriction leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem leviHarishChandraRankZero leviHarishChandraTheorem leviPiOpenSubgroup leviQuasicuspidalDecomposition leviQuasicuspidalDecomposition_of_inputs levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_determinantUnitSubgroup_iff_valuation mem_leviPiOpenSubgroup normalizedAbs_eq_one_iff
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV

/-- The exact quasicuspidal decomposition proposition, including the empty-product
boundary case, with no additional representation hypotheses. -/
theorem leviQuasicuspidalDecomposition 
    (F : Type uF) [Field F] (T : LocalFieldData F) {n : ℕ} (B : BlockShape n) :
    LeviQuasicuspidalDecompositionTheorem.{uF, uV} F T B := by
  cases n with
  | zero =>
    let := T.topology
    have hsize (i : Fin B.length) : B.size i ≤ 0 := by
      calc
        B.size i ≤ ∑ j, B.size j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = 0 := B.sum_eq
    let : IsEmpty (Fin B.length) :=
      ⟨fun i => (Nat.not_lt_of_ge (hsize i)) (B.positive i)⟩
    have hqc (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F)) :
        IsLeviQuasicuspidal B A.representation := by
      intro S hS
      exact (hS (Subsingleton.elim _ _)).elim
    exact SmoothRep.decomposition_of_natural_idempotent
      (fun A => IsLeviQuasicuspidal B A.representation)
      (fun A => Representation.IntertwiningMap.id A.representation)
      (fun _ _ _ _ => rfl) (fun _ _ => rfl)
      (fun A => hqc _) (fun _ _ _ => rfl)
  | succ n =>
    exact leviQuasicuspidalDecomposition_of_inputs T B
      (determinantUnitIsotypic_isCompl T B)
      (compactCoefficientFixedLevelFiniteness F T (n + 1) (Nat.succ_pos n) B)
      (determinantUnitTotalIsotypic_compact T B)
      (determinantUnitTotalIsotypic_exhaust T B)
      leviHarishChandraTheorem

end Langlands.AllField.CuspidalSupport
