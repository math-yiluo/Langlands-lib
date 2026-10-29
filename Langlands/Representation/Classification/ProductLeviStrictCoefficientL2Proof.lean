import Langlands.Representation.Classification.ProductLeviStrictCoefficientL2Statement
import Langlands.Representation.Classification.ProductLeviSquareIntegrableSufficiencyProof

/-! # Exact coefficient L² interface from the published product-Levi helper -/

namespace Langlands

universe uF uV

/-- Every supplied coefficient is in L² under strict fundamental Jacquet bounds. -/
theorem glProductLeviStrictCoefficientL2 :
    GLProductLeviStrictCoefficientL2Statement.{uF, uV} := by
  intro hcount p _ F T
  let := T.topology
  intro n C
  let := T.leviTopologicalGroup C
  intro Q _ _ μ _ V _ _ ρ hadm hstrict c ℓ v
  exact ProductLeviSquareIntegrable.memLp_two_of_strictFundHypothesis
    T C hcount μ ρ hadm hstrict c ℓ v

end Langlands
