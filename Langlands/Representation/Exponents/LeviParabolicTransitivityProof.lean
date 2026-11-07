import Langlands.Representation.Exponents.LeviParabolicTransitivityStatement
import Langlands.Representation.Exponents.LeviParabolicTransitivityReduction
import Langlands.GroupScheme.Rational.NestedParabolicPointDecompositionProof

/-! # Transitivity for the original represented parabolic triples -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.1.4 for the supplied actual parabolic triples and the canonical
represented-Levi functors, with no additional decomposition premise. -/
theorem leviParabolicTransitivity : LeviParabolicTransitivityStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q L U PL NL p m n hp hm hn hmul
    q l uQ hq hl huQ hmulQ pL mL nL hpL hmL hnL hmulL hPQ hM hPL
  obtain ⟨hNL, hprod, _⟩ :=
    nestedParabolicPointDecomposition k G hG P M N Q L U PL NL
      p m n hp hm hn hmul q l uQ hq hl huQ hmulQ
      pL mL nL hpL hmL hnL hmulL hPQ hM hPL
  exact leviParabolicTransitivity_of_radical_decomposition
    p m n hp hm hn hmul q l uQ hq hl huQ hmulQ
    pL mL nL hpL hmL hnL hmulL hPQ hM hPL hNL hG hprod

end Langlands.Aubert.General.RepresentedParabolic
