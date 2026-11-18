import Langlands.Representation.Archimedean.ComplexGenericLargeProof
import Langlands.Representation.Archimedean.ComplexGenericStandardInjectiveReduction
import Langlands.Representation.Archimedean.ComplexLargePrincipalSeriesProof

/-!
# Irreducible admissible generic `(𝔤𝔩_n(ℂ), U(n))`-modules have standard-module parameters

`complexGenericStandardParameter` proves `ComplexGenericStandardParameterStatement`: every
irreducible admissible generic `(𝔤𝔩_n(ℂ), U(n))`-module has the standard-module parameter of
some list of complex characters.

The proof applies `complexGenericStandardParameter_of_large` to two proved Library theorems:

* `complexGenericLarge : ComplexGenericLargeStatement` (Kostant 1978, Theorem 3.9): an
  irreducible admissible generic module is large;
* `complexLargePrincipalSeries : ComplexLargePrincipalSeriesStatement` (Vogan 1978,
  Theorem 6.2 (a) ⇒ (f), for `GL_n(ℂ)`): an irreducible admissible large module has a
  standard-module parameter.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

universe uV

/-- **Generic modules have standard-module parameters** (`GL_n(ℂ)`): every irreducible
admissible generic `(𝔤𝔩_n(ℂ), U(n))`-module embeds in a principal series of `GL_n(ℂ)` whose
`U(n)`-finite functions it then exhausts. A generic module is large (Kostant), and a large
module has a standard-module parameter (Vogan). -/
theorem complexGenericStandardParameter : ComplexGenericStandardParameterStatement.{uV} :=
  complexGenericStandardParameter_of_large complexGenericLarge complexLargePrincipalSeries

end Langlands.Archimedean
