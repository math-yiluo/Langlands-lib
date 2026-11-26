import Langlands.Global.EisensteinConstantTerm.UnfoldingReduction
import Langlands.Global.EisensteinConstantTerm.UnfoldingStructureProof

/-! # The integration identity of the geometric lemma (proof) -/

universe u

namespace Langlands.Global

/-- **The integration identity of the geometric lemma** (Bernstein–Lapid, proof of Lemma 6.10).
The subgroup structure `UnfoldingSubgroupStructure` follows from the dynamic description of the
parabolics (`unfoldingSubgroupStructure_of_datum`), and the identity follows from it
(`geometricLemmaUnfolding_of_structure`). -/
theorem geometricLemmaUnfolding : GeometricLemmaUnfoldingStatement.{u} := by
  intro F _ _ G P U Q V P' U' Q' V' _ _ _ _ _ _ _ _ p _ iU q iV _ w f iU' g' iV' _ _ _
    hG hP hU hQ hV hP' hU' hQ' hV' hDat h hm hhU hhP y hfin
  exact geometricLemmaUnfolding_of_structure F p iU q iV w f iU' g' iV' hU hV hU' hV'
    (unfoldingSubgroupStructure_of_datum F p iU q iV w f iU' g' iV' hG hP hU hQ hV hP' hU'
      hQ' hV' hDat) h hm hhU hhP y hfin

end Langlands.Global
