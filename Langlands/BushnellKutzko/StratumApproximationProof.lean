import Langlands.BushnellKutzko.StratumApproximationReduction
import Langlands.BushnellKutzko.MinimalCriticalExponentProof
import Langlands.BushnellKutzko.StratumEquivalenceProof
import Langlands.BushnellKutzko.RefinementProof
import Langlands.BushnellKutzko.PureStratumSimpleApproximationProof
import Langlands.BushnellKutzko.SimpleStratumCorestrictionCongruenceProof
import Langlands.BushnellKutzko.CriticalDerivedStratumProof

/-! # Approximation of pure strata: proof (BK93 (2.4.1)–(2.4.2), printed pp. 65–66)

Proof of `StratumApproximationStatement`. The reduction `stratumApproximationReduction` derives
it from six propositions: BK93 (1.4.15) (`MinimalCriticalExponentStatement`), (1.5.2) and (2.1.4)
(`StratumEquivalenceStatement`), (2.2.8) (`RefinementStatement`), (2.4.1)(i) with divisibility
for the witness (`PureStratumSimpleApproximationStatement`), (2.4.1)(ii)(c)
(`SimpleStratumCorestrictionCongruenceStatement`) and (2.4.1)(iii)
(`CriticalDerivedStratumStatement`). This module applies the reduction to their proofs.
-/

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK93 (2.4.1), (2.4.2), printed pp. 65–66.** Every pure stratum has an equivalent simple
stratum with the same chain and integers; every such simple stratum has ramification index and
residue degree dividing those of the pure stratum, and a pure equivalent stratum is simple exactly
when its generated field has minimal degree; equivalent simple strata satisfy the
tame-corestriction congruence; the critical derived stratum of a pure stratum at its critical
level is equivalent to a simple stratum; and every pure stratum has a defining sequence. -/
theorem stratumApproximation : StratumApproximationStatement.{uF, uV} :=
  stratumApproximationReduction
    minimalCriticalExponent.{uF, uV, uV}
    stratumEquivalence.{uF, uV}
    refinement.{uF, uV, uV}
    pureStratumSimpleApproximation.{uF, uV}
    simpleStratumCorestrictionCongruence.{uF, uV}
    criticalDerivedStratum.{uF, uV}

end Langlands.BushnellKutzko
