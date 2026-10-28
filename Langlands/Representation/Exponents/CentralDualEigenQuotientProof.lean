import Langlands.Representation.Exponents.CentralDualEigenQuotientStatement
import Langlands.Representation.Classification.MaximalConeQuotient

/-!
# Central dual eigenfunctionals give irreducible admissible scalar quotients

This derived generic prerequisite packages the published quotient extraction
theorem with an existential hypothesis on the full algebraic dual functional.
-/

namespace Langlands

/-- The closed central dual eigenfunctional quotient statement, obtained by
unpacking the functional and applying the published generic extraction theorem. -/
theorem centralDualEigenQuotient.{uG, uC, uV} :
    CentralDualEigenQuotientStatement.{uG, uC, uV} := by
  intro G _ _ _ hG C _ z hz χ V _ _ ρ hfin hadm ⟨φ, hφ, heig⟩
  exact MaximalConeQuotient.exists_irreducible_quotient hG z hz χ ρ hfin hadm φ hφ heig

end Langlands
