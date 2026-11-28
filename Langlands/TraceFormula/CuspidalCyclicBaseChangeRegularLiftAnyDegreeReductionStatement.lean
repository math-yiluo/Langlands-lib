import Langlands.TraceFormula.CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement
import Langlands.TraceFormula.CuspidalCyclicLiftSpectralComparisonStatement
import Langlands.BaseChange.RegularNormTraceNonvanishingStatement

/-!
# Reduction of the regular cuspidal cyclic lift to the spectral comparison

Statement only (no proof). The cuspidal cyclic lift with the regular σ-lift identity,
`CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement`, follows from the spectral comparison
`CuspidalCyclicLiftSpectralComparisonStatement` and the local nonvanishing statement
`RegularNormTraceNonvanishingStatement`. This is the local end of the argument of
Arthur–Clozel (1989), Chapter 1, §6.3, printed pp. 54–57: the list of lifts is nonempty
because the character of the supercuspidal component at `v₁` is not zero; the isomorphisms at
the split places come from proportionality of characters; and the constant at a place with a
single place above it is nonzero because some regular concordant pair with norm determinants
has nonzero trace. See the paired Markdown.
-/

namespace Langlands.TraceFormula

universe u uV uW

/-- The spectral comparison `CuspidalCyclicLiftSpectralComparisonStatement.{u, uV, uW}` and
the local nonvanishing statement `RegularNormTraceNonvanishingStatement.{u, u, u}` imply the
cuspidal cyclic lift with the regular σ-lift identity,
`CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement.{u, uV, uW}`. -/
def CuspidalCyclicBaseChangeRegularLiftAnyDegreeReductionStatement : Prop :=
  CuspidalCyclicLiftSpectralComparisonStatement.{u, uV, uW} →
    Langlands.BaseChange.RegularNormTraceNonvanishingStatement.{u, u, u} →
      CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement.{u, uV, uW}

end Langlands.TraceFormula
