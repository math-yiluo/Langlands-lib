import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetVanishingSmoothPieces
import Langlands.AllFieldBZ.Representation.CuspidalSupport.ProperInductionProof
import Langlands.AllFieldBZ.Representation.Filtration.QuasicuspidalVanishingProof
import Langlands.AllFieldBZ.Representation.Geometric.GeometricLemmaProof
import Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem CompactCoefficientFixedLevelFinitenessTheorem DeterminantUnitCornerStructureStatement DeterminantUnitSmoothDualStatement GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement LeviCuspidalConstituentTheorem LeviHarishChandraConverseTheorem LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem LeviQuasicuspidalDecompositionTheorem MinimalNonzeroJacquetTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement PadicProperRefinedInductionTheorem ProperRefinedInductionTheorem TotalConjugatingCountTheorem compactCoefficientFixedLevelFiniteness compactCoefficientFixedLevelFiniteness_of_cornerStructure continuous_determinantUnitInclusion cuspidalDatum_eq_of_equiv determinantUnitCompactOpenCofinal determinantUnitCornerStructure determinantUnitInclusion determinantUnitInclusion_apply determinantUnitIsotypic_isCompl determinantUnitLocallyCompactSpace determinantUnitNonarchimedean determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal determinantUnitTotalIsotypic_compact determinantUnitTotalIsotypic_exhaust exists_leviPiOpenSubgroup_subset geometricPieceFunctor_subsingleton_of_proper_source geometricPieceInducingFunctor geometricPieceSmoothFunctor geometricPieceSmoothFunctor_obj_toRep geometricPieceSmoothFunctor_toRep glCuspidalTensorAssociation induced_quasicuspidal_subrepresentation_subsingleton isCompact_leviPiOpenSubgroup isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem leviHarishChandraRankZero leviHarishChandraTheorem leviPiOpenSubgroup leviQuasicuspidalDecomposition leviQuasicuspidalDecomposition_of_inputs levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_determinantUnitSubgroup_iff_valuation mem_leviPiOpenSubgroup minimalNonzeroJacquet minimalWeylTransportQuasicuspidal nonassociatedJacquetSubquotients nonassociatedJacquetSubquotients_rankZero normalizedAbs_eq_one_iff normalizedRefinedInductionFunctor_subsingleton padicLeviFiltrationNoQuasicuspidalSubquotients padicProperRefinedInduction totalConjugatingCount
open Langlands.GeneralLinear
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicBruhatMatrixExistenceTheorem PadicBruhatWeylReflectionTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicParabolicOrbitJacquetComparison PadicParabolicSupportGradedTheorem PadicParabolicSupportJacquetComparison PadicStandardIntersectionsTheorem closedSubgroupOrbitOrdering_of_finiteOrbitOrdering correctionSubgroupDiagonalHaar geometricLemma_of_orderedCosets geometricLemma_of_supportGraded geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicBruhatMatrixExistence padicBruhatWeylReflection padicGeometricLemma padicParabolicBruhat padicParabolicOrbitJacquetComparison padicParabolicSupportGradedTheorem padicParabolicSupportJacquetComparison padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor parabolicSupportGradedCompactSmoothIso refinedLeviModulus_of_diagonal supportCoinvariantsImageHom_injective supportCoinvariantsImageIso supportImageNatIso supportImageQuotientHom supportImageQuotientHom_bijective supportImageQuotientIso supportImageToQuotient supportImageToQuotient_ker supportImageToQuotient_on_support supportImageToQuotient_surjective
open Langlands.AllFieldBZ.Geometric
open CategoryTheory
universe uF uV

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData) (n : ℕ)

set_option maxHeartbeats 800000 in
/-- Every quasicuspidal smooth subquotient of the Jacquet module of
quasicuspidal induction between nonassociated Levis is zero. -/
theorem nonassociatedJacquetSubquotients :
    NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact nonassociatedJacquetSubquotients_rankZero F T
  classical
  let := T.topology
  intro B C ρ hρ hBC
  obtain ⟨S, R, hS, hR, m, e, a, s, hs⟩ :=
    Langlands.AllFieldBZ.Geometric.padicGeometricLemma.{uF, uV} F T n hn B C
  apply padicLeviFiltrationNoQuasicuspidalSubquotients.{max uF uV, uF} F T n C
    ((T.normalizedJacquetFunctor C).obj
      ((T.normalizedParabolicInductionFunctor B).obj ρ))
    m (objectFiltrationAt s ρ)
  intro i
  obtain ⟨j⟩ := hs i
  let w := e (a i)
  let Q := (geometricPieceSmoothFunctor F T B C w.val (S w) (R w)
    (hS w).2.1 (hR w).2.1).obj ρ
  have hQ : Q.obj = (Langlands.AllFieldBZ.Geometric.geometricPieceFunctor T B C w.val (S w) (R w)
      (hS w).2.1 (hR w).2.1).obj ρ :=
    geometricPieceSmoothFunctor_obj_toRep F T B C w.val (S w) (R w)
      (hS w).2.1 (hR w).2.1 ρ
  refine ⟨Q, ⟨Representation.equivOfIso
    (j.app ρ ≪≫ eqToIso hQ.symm)⟩, ?_⟩
  intro D hD hq
  by_cases hfull : refinedParabolic F.Carrier B (S w) = ⊤
  · have hp := target_refinement_proper_of_nonassociated_source_full B C hBC
      w.val (S w) (R w) (hS w) (hR w) hfull
    exact padicProperRefinedInduction.{uF, uV} F T n hn C (R w) hp
      ((geometricPieceInducingFunctor F T B C w.val (S w) (R w)
        (hS w).2.1 (hR w).2.1).obj ρ) D hD hq
  · have hz := geometricPieceFunctor_subsingleton_of_proper_source F T B C
      w.val (S w) (R w) (hS w).2.1 (hR w).2.1 ρ hρ hfull
    have hzeroQ : Subsingleton Q := by
      change Subsingleton Q.obj
      rw [hQ]
      exact hz
    let := hzeroQ
    exact subsingleton_of_isSubquotient hD

end Langlands.AllFieldBZ.CuspidalSupport
