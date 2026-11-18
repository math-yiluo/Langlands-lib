import Langlands.Representation.Archimedean.ComplexStandardLanglandsQuotientProof
import Langlands.Representation.Archimedean.ComplexLargePrincipalSeriesReduction
import Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleReduction
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientProof
import Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleProof
import Langlands.Representation.Archimedean.ComplexBlockLanglandsQuotient
import Langlands.Representation.Archimedean.ComplexBlockChartIntegralProof
import Langlands.Representation.Archimedean.ComplexBlockParabolicIntegrationProof
import Langlands.Representation.Archimedean.ComplexTemperedStandardIrreducibleProof

/-!
# Large irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-modules are principal series

`complexLargePrincipalSeries` proves `ComplexLargePrincipalSeriesStatement` (Vogan 1978,
Theorem 6.2 (a) ⇒ (f), for `GL_n(ℂ)`): every irreducible admissible large
`(𝔤𝔩_n(ℂ), U(n))`-module has the standard-module parameter of some list of complex characters.

The proof composes proved Library theorems:

* `ComplexLargePrincipalSeriesProof.standardLanglandsQuotient` (this module) proves
  `ComplexStandardLanglandsQuotientStatement` by applying `complexBlockLanglandsQuotient` to
  `complexBlockChartIntegrable`, `complexBlockParabolicIntegration` and
  `complexTemperedStandardIrreducible`;
* `complexLargeStandardIrreducibleReduction` turns it and `complexLargeStandardIrreducible`
  into `ComplexLargeLanglandsQuotientInjectiveStatement`;
* `complexLargePrincipalSeriesReduction` combines `complexLanglandsQuotient` with that
  injectivity statement.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

universe uV

namespace ComplexLargePrincipalSeriesProof

/-- The Langlands quotient of a Langlands-ordered complex standard module: its `U(n)`-finite
functions have a largest proper `(𝔤, K)`-submodule. -/
theorem standardLanglandsQuotient : ComplexStandardLanglandsQuotientStatement :=
  Langlands.Archimedean.complexStandardLanglandsQuotient

/-- Vogan's injectivity step for `GL_n(ℂ)`: a nonzero intertwining map from a Langlands-ordered
standard module into an irreducible admissible large `(𝔤𝔩_n(ℂ), U(n))`-module is injective. -/
theorem largeLanglandsQuotientInjective :
    ComplexLargeLanglandsQuotientInjectiveStatement.{uV} :=
  complexLargeStandardIrreducibleReduction standardLanglandsQuotient
    complexLargeStandardIrreducible

end ComplexLargePrincipalSeriesProof

/-- **Large modules are principal series** (Vogan 1978, Theorem 6.2 (a) ⇒ (f), for `GL_n(ℂ)`):
every irreducible admissible large `(𝔤𝔩_n(ℂ), U(n))`-module has the standard-module parameter
of some list of complex characters. -/
theorem complexLargePrincipalSeries : ComplexLargePrincipalSeriesStatement.{uV} :=
  complexLargePrincipalSeriesReduction complexLanglandsQuotient
    ComplexLargePrincipalSeriesProof.largeLanglandsQuotientInjective

end Langlands.Archimedean
