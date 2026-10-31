import Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.CuspidalSupport.JacquetVanishingSmoothPieces
import Langlands.Representation.CuspidalSupport.ProperInductionProof
import Langlands.Representation.Filtration.QuasicuspidalVanishingProof
import Langlands.Representation.Geometric.GeometricLemmaProof

/-! BZ77 2.13(b): nonassociated Jacquet modules have no nonzero
quasicuspidal subquotients. -/

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
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
    padicGeometricLemma.{uF, uV} p F T n hn B C
  apply padicLeviFiltrationNoQuasicuspidalSubquotients.{max uF uV, uF} p F T n C
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
  by_cases hfull : refinedParabolic F.Carrier B (S w) = ⊤
  · have hp := target_refinement_proper_of_nonassociated_source_full B C hBC
      w.val (S w) (R w) (hS w) (hR w) hfull
    exact padicProperRefinedInduction.{uF, uV} p F T n hn C (R w) hp
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

end Langlands.CuspidalSupport
