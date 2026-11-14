import Langlands.AllFieldBZ.Representation.CuspidalSupport.CompactCoefficientFinitenessProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.HarishChandraAssembly
import Langlands.AllFieldBZ.Representation.CuspidalSupport.LeviCompactPart
import Langlands.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem CompactCoefficientFixedLevelFinitenessTheorem DeterminantUnitCornerStructureStatement DeterminantUnitSmoothDualStatement GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement LeviCuspidalConstituentTheorem LeviHarishChandraConverseTheorem LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem LeviQuasicuspidalDecompositionTheorem NonassociatedJacquetSubquotientsTheorem compactCoefficientFixedLevelFiniteness compactCoefficientFixedLevelFiniteness_of_cornerStructure continuous_determinantUnitInclusion cuspidalDatum_eq_of_equiv determinantUnitCompactOpenCofinal determinantUnitCornerStructure determinantUnitInclusion determinantUnitInclusion_apply determinantUnitIsotypic_isCompl determinantUnitLocallyCompactSpace determinantUnitNonarchimedean determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal determinantUnitTotalIsotypic_compact determinantUnitTotalIsotypic_exhaust exists_leviPiOpenSubgroup_subset glCuspidalTensorAssociation isCompact_leviPiOpenSubgroup isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem leviHarishChandraRankZero leviHarishChandraTheorem leviPiOpenSubgroup leviQuasicuspidalDecomposition leviQuasicuspidalDecomposition_of_inputs levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_determinantUnitSubgroup_iff_valuation mem_leviPiOpenSubgroup normalizedAbs_eq_one_iff
open Langlands.GeneralLinear
universe uF uV

/-- The exact quasicuspidal decomposition proposition, including the empty-product
boundary case, with no additional representation hypotheses. -/
theorem leviQuasicuspidalDecomposition (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) :
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
    have hqc (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) :
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

end Langlands.AllFieldBZ.CuspidalSupport
