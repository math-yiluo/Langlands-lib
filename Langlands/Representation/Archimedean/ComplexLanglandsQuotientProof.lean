import Langlands.Representation.Archimedean.ComplexLanglandsQuotientReduction
import Langlands.Representation.Archimedean.ComplexLanglandsSubrepresentationProof
import Langlands.Representation.Archimedean.ComplexContragredientProof
import Langlands.Representation.Archimedean.ComplexStandardDualityProof

/-!
# The Langlands quotient statement for complex general linear groups

`complexLanglandsQuotient` proves `ComplexLanglandsQuotientStatement`: every irreducible
admissible `(𝔤𝔩_n(ℂ), U(n))`-module receives a nonzero intertwining map from the
`U(n)`-finite functions of the standard module of some list of `n` complex characters whose
exponents have non-increasing real parts.

The proof applies the Library reduction `complexLanglandsQuotientReduction`
(`S1 → S2 → S3 → ComplexLanglandsQuotientStatement`) to the three proved Library theorems

* S1: `complexLanglandsSubrepresentation` (subrepresentation form of the Langlands
  classification),
* S2: `ComplexContragredient.complexContragredientStatement` (the `U(n)`-finite contragredient),
* S3: `complexStandardDuality` (duality of standard modules with inverse characters).

See the paired Markdown.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

universe uV

/-- `ComplexLanglandsQuotientStatement` follows from the subrepresentation form S1, since the
premises S2 and S3 of `complexLanglandsQuotientReduction` are proved in the Library. -/
theorem complexLanglandsQuotient_of_subrepresentation
    (hS1 : ComplexLanglandsSubrepresentationStatement.{uV}) :
    ComplexLanglandsQuotientStatement.{uV} :=
  complexLanglandsQuotientReduction hS1 ComplexContragredient.complexContragredientStatement
    complexStandardDuality

/-- The Langlands classification of irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-modules, quotient
form (Knapp 1994, Theorem 4): every irreducible admissible module `(ρ, π)` receives a nonzero
intertwining map from the `U(n)`-finite functions of the standard module of some list of `n`
complex characters whose exponents have non-increasing real parts. -/
theorem complexLanglandsQuotient : ComplexLanglandsQuotientStatement.{uV} :=
  complexLanglandsQuotient_of_subrepresentation complexLanglandsSubrepresentation

end Langlands.Archimedean
