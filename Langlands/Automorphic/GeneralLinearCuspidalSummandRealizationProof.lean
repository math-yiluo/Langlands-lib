import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationFromDensity
import Langlands.Automorphic.GeneralLinearSummandFormsDenseProof

/-! # Irreducible cuspidal `L²` summands of `GL_n` come from cuspidal operator realizations

The summand-to-realization direction of Getz–Hahn, Theorem 9.7.3: the implication
`generalLinearCuspidalSummandRealizationFromDensity` applied to the density theorem
`generalLinearSummandFormsDense`. -/

universe u

namespace Langlands.Automorphic.GroupSchemeFunctions

/-- **Irreducible cuspidal `L²` summands come from cuspidal operator realizations**
(Getz–Hahn, Theorem 9.7.3, with Theorem 9.7.1 and Lemma 9.7.2). For every nonzero closed
invariant subspace `P` of the full almost-everywhere cuspidal subspace of
`L²([GL_{r+1}])` with no closed invariant subspaces other than `0` and itself, there are a
cuspidal operator realization `R` and a linear map `Φ` sending each vector of `R` to the `L²`
class of the function it induces on the quotient, with the closure of the range of `Φ` equal
to `P`. -/
theorem generalLinearCuspidalSummandRealization :
    GeneralLinearCuspidalSummandRealizationStatement.{u} :=
  generalLinearCuspidalSummandRealizationFromDensity generalLinearSummandFormsDense

end Langlands.Automorphic.GroupSchemeFunctions
