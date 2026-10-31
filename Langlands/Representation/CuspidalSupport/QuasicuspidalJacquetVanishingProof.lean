import Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.Filtration.SubsingletonProof
import Langlands.Representation.Geometric.GeometricLemmaProof

/-! BZ77 2.13(a): vanishing when no target refinement is associated
to the source Levi. -/

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) (n : ℕ)

/-- The Jacquet module of quasicuspidal induction is zero when no standard
refinement of the target Levi is associated to the source Levi. -/
theorem quasicuspidalJacquetVanishing :
    QuasicuspidalJacquetVanishingTheorem.{uF, uV} F T n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact quasicuspidalJacquetVanishing_rankZero F T
  let := T.topology
  intro B C ρ hρ hBC
  obtain ⟨S, R, hS, hR, m, e, a, s, hs⟩ :=
    padicGeometricLemma.{uF, uV} p F T n hn B C
  apply objectRepFiltrationSubsingleton ℂ (C.Levi F.Carrier)
    ((jacquetInductionFunctor T B C).obj ρ)
    m (objectFiltrationAt s ρ)
  intro i
  obtain ⟨j⟩ := hs i
  have hp := source_refinement_proper_of_no_associated_refinement B C hBC
    (e (a i)).val (S (e (a i))) (R (e (a i)))
    (hS (e (a i))) (hR (e (a i)))
  have hz := geometricPieceFunctor_subsingleton_of_proper_source F T B C
    (e (a i)).val (S (e (a i))) (R (e (a i)))
    (hS (e (a i))).2.1 (hR (e (a i))).2.1 ρ hρ hp
  exact ⟨fun x y => (Representation.equivOfIso (j.app ρ)).toLinearEquiv.injective
    (hz.elim _ _)⟩

end Langlands.CuspidalSupport
