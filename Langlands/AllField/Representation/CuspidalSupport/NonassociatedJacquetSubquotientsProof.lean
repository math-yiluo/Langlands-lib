import Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
import Langlands.AllField.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.AllField.Representation.CuspidalSupport.JacquetVanishingSmoothPieces
import Langlands.AllField.Representation.CuspidalSupport.ProperInductionProof
import Langlands.AllField.Representation.Filtration.QuasicuspidalVanishingProof
import Langlands.AllField.Representation.Geometric.GeometricLemmaProof
/-! BZ77 2.13(b): nonassociated Jacquet modules have no nonzero
quasicuspidal subquotients. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem GLCuspidalTensorStatement MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement PadicProperRefinedInductionTheorem ProperRefinedInductionTheorem TotalConjugatingCountTheorem determinantUnitInclusion determinantUnitRestriction determinantUnitSubgroup geometricPieceFunctor_subsingleton_of_proper_source geometricPieceInducingFunctor geometricPieceSmoothFunctor geometricPieceSmoothFunctor_obj_toRep geometricPieceSmoothFunctor_toRep induced_quasicuspidal_subrepresentation_subsingleton leviHarishChandraTheorem leviQuasicuspidalDecomposition levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup minimalNonzeroJacquet minimalWeylTransportQuasicuspidal nonassociatedJacquetSubquotients nonassociatedJacquetSubquotients_rankZero normalizedRefinedInductionFunctor_subsingleton padicLeviFiltrationNoQuasicuspidalSubquotients padicProperRefinedInduction totalConjugatingCount
open Langlands.AllField.CuspidalSupport

open _root_.CategoryTheory
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicOrbitJacquetComparison PadicParabolicSupportGradedTheorem PadicParabolicSupportJacquetComparison PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricLemma_of_orderedCosets geometricLemma_of_supportGraded geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicGeometricLemma padicParabolicBruhat padicParabolicOrbitJacquetComparison padicParabolicSupportGradedTheorem padicParabolicSupportJacquetComparison padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor parabolicSupportGradedCompactSmoothIso refinedLeviModulus_of_diagonal supportCoinvariantsImageHom_injective supportCoinvariantsImageIso supportImageNatIso supportImageQuotientHom supportImageQuotientHom_bijective supportImageQuotientIso supportImageToQuotient supportImageToQuotient_ker supportImageToQuotient_on_support supportImageToQuotient_surjective
open Langlands.AllField.Geometric

universe uF uV

variable (F : Type uF) [Field F]
  (T : LocalFieldData F) (n : ℕ)

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
    padicGeometricLemma.{uF, uV} F T n hn B C
  apply padicLeviFiltrationNoQuasicuspidalSubquotients.{max uF uV, uF} F T n C
    ((T.normalizedJacquetFunctor C).obj
      ((T.normalizedParabolicInductionFunctor B).obj ρ))
    m (objectFiltrationAt s ρ)
  intro i
  obtain ⟨j⟩ := hs i
  let w := e (a i)
  let Q := (geometricPieceSmoothFunctor F T B C w.val (S w) (R w)
    (hS w).2.1 (hR w).2.1).obj ρ
  have hQ : Q.obj = (geometricPieceFunctor T B C w.val (S w) (R w)
      (hS w).2.1 (hR w).2.1).obj ρ :=
    geometricPieceSmoothFunctor_obj_toRep F T B C w.val (S w) (R w)
      (hS w).2.1 (hR w).2.1 ρ
  refine ⟨Q, ⟨Representation.equivOfIso
    (j.app ρ ≪≫ eqToIso hQ.symm)⟩, ?_⟩
  intro D hD hq
  by_cases hfull : refinedParabolic F B (S w) = ⊤
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

end Langlands.AllField.CuspidalSupport
