import Langlands.Representation.RankinSelberg.LanglandsPairLPolynomialReduction
import Langlands.Representation.RankinSelberg.LanglandsTypeLFactorProof
import Langlands.Representation.Classification.RegularLanglandsExhaustionProof
import Langlands.Representation.Classification.RegularLanglandsDataUniquenessProof

/-!
# Existence of the L-factor of every irreducible admissible pair

JPSS 1983, (9.4), printed page 458. Exhaustion presents each member of the pair
as the head of a standard module with saturated block carriers, the
standard-module statement (9.4)(3) supplies the L-polynomial of that pair of
standard modules, and data uniqueness certifies it for every tempered
presentation on the original block-carrier universes.
-/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- JPSS 1983, (9.4), printed page 458: every pair of irreducible admissible
representations has an L-polynomial defined through the Langlands
classification. -/
theorem langlandsPairLFactorExistence :
    LanglandsPairLFactorExistenceStatement.{uF, uV, uW} := by
  intro p _ F ψ ν r t π σ hπ haπ hσ haσ
  obtain ⟨d, hd⟩ := glRegularLanglandsExhaustion.{uF, uV} p F F.canonicalTopologicalData
    (r + 1) (Nat.succ_pos r) π hπ haπ
  obtain ⟨e, he⟩ := glRegularLanglandsExhaustion.{uF, uW} p F F.canonicalTopologicalData
    (t + 1) (Nat.succ_pos t) σ hσ haσ
  obtain ⟨P, -, hP, -, -⟩ := langlandsTypeLFactor.{uF, max uF uV, max uF uW} p F ψ ν r t d e
  exact ⟨P, isLanglandsPairLPolynomial_of_saturatedData F ψ ν.val π σ
    glRegularLanglandsDataUniqueness.{uF, uV} glRegularLanglandsDataUniqueness.{uF, uW}
    d e hd.isLanglandsQuotient he.isLanglandsQuotient hP⟩

end Langlands.RankinSelberg
