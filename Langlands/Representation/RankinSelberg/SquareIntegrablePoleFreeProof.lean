import Langlands.Representation.RankinSelberg.TemperedLFactorStatement
import Langlands.Representation.RankinSelberg.SquareIntegrableLPolynomialNonvanishingProof
import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTypeOfGenericityProof
import Langlands.Representation.Classification.SquareIntegrableGenericityProof

/-!
# Pole-freeness of square-integrable Rankin–Selberg L-factors

Intrinsic square-integrable genericity supplies full Whittaker type in each
carrier universe. Symmetric polynomial existence and sharp analytic
nonvanishing then give the closed pole-freeness statement.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker Polynomial

universe uF uV uW

/-- Every irreducible square-integrable pair has a symmetric L-polynomial
that is nonvanishing throughout the open unit disk. -/
theorem squareIntegrablePoleFree :
    SquareIntegrablePoleFreeStatement.{uF,uV,uW} := by
  intro p _ F ψ ν r t V _ _ W _ _ π σ hiπ hsπ hiσ hsσ
  have hπ := squareIntegrableWhittakerType_of_genericity.{uF,uV}
    F (Classification.squareIntegrableGenericity.{uF,uV}
      F F.canonicalTopologicalData) ψ r π hiπ hsπ
  have hσ := squareIntegrableWhittakerType_of_genericity.{uF,uW}
    F (Classification.squareIntegrableGenericity.{uF,uW}
      F F.canonicalTopologicalData) ψ t σ hiσ hsσ
  obtain ⟨P, hP⟩ :=
    symmetricLPolynomialExists.{uF,uV,uW} p F ψ ν r t V W π σ hπ hσ
  exact ⟨P, hP, fun _ hz =>
    hP.eval_ne_zero_of_squareIntegrable hiπ hsπ hiσ hsσ hz⟩

end Langlands.RankinSelberg
