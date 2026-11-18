import Langlands.Representation.Archimedean.ComplexBlockLanglandsQuotient
import Langlands.Representation.Archimedean.ComplexBlockChartIntegralProof
import Langlands.Representation.Archimedean.ComplexBlockParabolicIntegrationProof
import Langlands.Representation.Archimedean.ComplexTemperedStandardIrreducibleProof

/-!
# The Langlands quotient of a Langlands-ordered complex standard module

`complexStandardLanglandsQuotient : ComplexStandardLanglandsQuotientStatement`: for every list
`ds` of `n` complex characters in the Langlands order, the `(𝔤𝔩_n(ℂ), U(n))`-module of
`U(n)`-finite functions of `complexStandardModule n ds` has a largest proper
`(𝔤, K)`-submodule.

The proof applies the reduction `complexBlockLanglandsQuotient`
(`ComplexBlockLanglandsQuotientStatement`) to the proofs of its three hypotheses:

* `complexBlockChartIntegrable : ComplexBlockChartIntegrableStatement`;
* `complexBlockParabolicIntegration : ComplexBlockParabolicIntegrationStatement`;
* `complexTemperedStandardIrreducible : ComplexTemperedStandardIrreducibleStatement`.
-/

namespace Langlands.Archimedean

set_option autoImplicit false

/-- A Langlands-ordered complex standard module has a largest proper `(𝔤, K)`-submodule. This
gives the unique irreducible quotient of Knapp 1994, Theorem 4 (a), for the `(𝔤, K)`-module of
`U(n)`-finite functions. The finite length of the standard module and the Jordan–Hölder
multiplicity one in Badulescu–Renard 2010, Theorem 3.3 (i), are neither proved nor used here. -/
theorem complexStandardLanglandsQuotient : ComplexStandardLanglandsQuotientStatement :=
  complexBlockLanglandsQuotient complexBlockChartIntegrable complexBlockParabolicIntegration
    complexTemperedStandardIrreducible

end Langlands.Archimedean
