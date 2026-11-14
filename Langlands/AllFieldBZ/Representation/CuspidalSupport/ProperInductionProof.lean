import Langlands.AllFieldBZ.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.ProperInductionMaps
import Langlands.AllFieldBZ.Representation.CuspidalSupport.ProperInductionStatement
import Langlands.Representation.CuspidalSupport.ProperInductionProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.ProperInductionProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.ProperInductionProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem CompactCoefficientFixedLevelFinitenessTheorem DeterminantUnitCornerStructureStatement DeterminantUnitSmoothDualStatement GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement LeviCuspidalConstituentTheorem LeviHarishChandraConverseTheorem LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem LeviQuasicuspidalDecompositionTheorem NonassociatedJacquetSubquotientsTheorem PadicProperRefinedInductionTheorem ProperRefinedInductionTheorem compactCoefficientFixedLevelFiniteness compactCoefficientFixedLevelFiniteness_of_cornerStructure continuous_determinantUnitInclusion cuspidalDatum_eq_of_equiv determinantUnitCompactOpenCofinal determinantUnitCornerStructure determinantUnitInclusion determinantUnitInclusion_apply determinantUnitIsotypic_isCompl determinantUnitLocallyCompactSpace determinantUnitNonarchimedean determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal determinantUnitTotalIsotypic_compact determinantUnitTotalIsotypic_exhaust exists_leviPiOpenSubgroup_subset glCuspidalTensorAssociation induced_quasicuspidal_subrepresentation_subsingleton isCompact_leviPiOpenSubgroup isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem leviHarishChandraRankZero leviHarishChandraTheorem leviPiOpenSubgroup leviQuasicuspidalDecomposition leviQuasicuspidalDecomposition_of_inputs levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_determinantUnitSubgroup_iff_valuation mem_leviPiOpenSubgroup normalizedAbs_eq_one_iff padicProperRefinedInduction
open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllFieldBZ.Geometric
universe uF uV

/-- BZ77 section 2.4(d), in the full subquotient form given by section 2.4(a). -/
theorem padicProperRefinedInduction :
    PadicProperRefinedInductionTheorem.{uF, uV} := by
  intro F T n hn B
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro S hS A D hD hDc
  let I := (T.normalizedRefinedInductionFunctor B S).obj A
  obtain ⟨U, Q, hcompl, hU, hQ⟩ :=
    leviQuasicuspidalDecomposition.{uF, max uF uV} F T B I
  let : Subsingleton (SmoothRep.subrepresentation I U) :=
    induced_quasicuspidal_subrepresentation_subsingleton T B S hS A U hU
  let e := complementIsoOfSubsingleton B I U Q hcompl
  exact hQ D (SmoothRep.IsSubquotient.of_iso_right hD e) hDc

end Langlands.AllFieldBZ.CuspidalSupport
