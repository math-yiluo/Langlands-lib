import Langlands.TraceFormula.CyclicStableCuspidalDescentTraceIdentityStatement
import Langlands.TraceFormula.CyclicStableCuspidalSpectralComparisonStatement
import Langlands.Automorphic.Unramified.WeakBaseChangeFiberNormTraceStatement
import Langlands.BaseChange.TwistedTraceRegularNonvanishingStatement

/-!
# Reduction of the stable cuspidal descent with a trace identity to three statements

Statement only (no proof). The Library's
`Langlands.TraceFormula.CyclicStableCuspidalDescentTraceIdentityStatement` follows from

* `Langlands.TraceFormula.CyclicStableCuspidalSpectralComparisonStatement`: the identity
  `tr (Π_w(φ) ∘ A) = Σ_i a i · tr π_{i,v}(f)` at `v`, for fixed Haar measures, over a finite
  family of cuspidal `π_i` of which `Π` is a weak base change;
* `Langlands.Automorphic.Unramified.WeakBaseChangeFiberNormTraceStatement`: two cuspidal
  representations with the same weak base change have equal local traces on test functions
  with norm determinants;
* `Langlands.BaseChange.TwistedTraceRegularNonvanishingStatement`: an irreducible admissible
  representation with a σ-intertwiner has nonzero twisted trace on some test function supported
  in the σ-regular set.

This module states that implication; the paired Markdown explains the argument it encodes
(Arthur–Clozel 1989, Chapter 1, §6.3(b), printed p. 57).
-/

universe uF uE uV uW

namespace Langlands.TraceFormula

/-- **Reduction of the descent with a trace identity at `v`.** The spectral comparison at `v`
(`CyclicStableCuspidalSpectralComparisonStatement`), the equality of local traces on norm
determinants in a fibre of weak base change (`WeakBaseChangeFiberNormTraceStatement`) and the
nonvanishing of twisted traces on the σ-regular set (`TwistedTraceRegularNonvanishingStatement`,
for local fields in the universe of `F` and the algebras `F_v ⊗_F E` and representation spaces
of `E`) together imply `CyclicStableCuspidalDescentTraceIdentityStatement`, all at the universe
parameters `{uF, uE, uV, uW}`. -/
def CyclicStableCuspidalDescentTraceIdentityReductionStatement : Prop :=
  CyclicStableCuspidalSpectralComparisonStatement.{uF, uE, uV, uW} →
    Langlands.Automorphic.Unramified.WeakBaseChangeFiberNormTraceStatement.{uF, uE, uV, uW} →
    Langlands.BaseChange.TwistedTraceRegularNonvanishingStatement.{uF, max uF uE, uE} →
    CyclicStableCuspidalDescentTraceIdentityStatement.{uF, uE, uV, uW}

end Langlands.TraceFormula
