import Langlands.BaseChange.RegularSigmaLiftSquareIntegrableStatement
import Langlands.TraceFormula.CyclicStableCuspidalDescentTraceIdentityStatement
import Langlands.TraceFormula.SigmaDiscreteTwistedGlobalizationStatement

/-!
# Reduction of the regular σ-descent to two global statements and a local criterion

Statement only (no proof). This module states that the descent of σ-discrete series on
regular test functions, `SigmaDiscreteRegularDescentStatement`, follows from two global
statements, the twisted globalization of a σ-discrete series and the weak descent with a
trace identity of a σ-stable cusp, and from a local criterion, the square-integrability of a
generic unitarizable regular σ-descent. This is the
structure of the proof of Henniart–Lemaire (2011), II.6.16–II.6.17, printed pp. 131–132, and
of Arthur–Clozel (1989), Chapter 1, §6.3, printed pp. 54–57. See the paired Markdown.
-/

namespace Langlands.BaseChange

/-- The global twisted globalization `SigmaDiscreteTwistedGlobalizationStatement`, the global
descent with a trace identity `CyclicStableCuspidalDescentTraceIdentityStatement` and the
local square-integrability criterion `RegularSigmaLiftSquareIntegrableStatement`, with their number
fields and local fields in `Type`, the spaces of their global presentations and of the
representation of `GL_{r+1}` over the local base field in `Type`, and the space of the
σ-discrete series in `Type uW`, imply `SigmaDiscreteRegularDescentStatement` at the universes
`u, v, uV, uW`.

See Henniart–Lemaire II.6.16–II.6.17, printed pp. 131–132, and Arthur–Clozel I, §6.3,
printed pp. 54–57. -/
def SigmaDiscreteRegularDescentReductionStatement.{u, v, uV, uW} : Prop :=
  TraceFormula.SigmaDiscreteTwistedGlobalizationStatement.{0, 0, uW, 0} →
    TraceFormula.CyclicStableCuspidalDescentTraceIdentityStatement.{0, 0, 0, 0} →
      RegularSigmaLiftSquareIntegrableStatement.{0, 0, 0, uW} →
        SigmaDiscreteRegularDescentStatement.{u, v, uV, uW}

end Langlands.BaseChange
