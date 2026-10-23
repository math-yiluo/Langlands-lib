import Langlands.Representation.CuspidalSupport.ProperInductionMaps
import Langlands.Representation.CuspidalSupport.ProperInductionStatement
import Langlands.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof
import Langlands.Representation.Classification.SupercuspidalSupport

/-! Proper normalized refined induction has no nonzero quasicuspidal subquotients. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

/-- BZ77 section 2.4(d), in the full subquotient form given by section 2.4(a). -/
theorem padicProperRefinedInduction :
    PadicProperRefinedInductionTheorem.{uF, uV} := by
  intro p hp F T n hn B
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

end Langlands.CuspidalSupport
