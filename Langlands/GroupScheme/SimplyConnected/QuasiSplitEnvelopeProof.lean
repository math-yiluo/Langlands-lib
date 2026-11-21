import Langlands.GroupScheme.SimplyConnected.QuasiSplitEnvelopeReduction
import Langlands.GroupScheme.SimplyConnected.NonmultipliableCorootSpanProof
import Langlands.GroupScheme.Rational.MaximalSplitSubgroupProof

/-! # Proof that a simply connected group has a quasi-split simply connected envelope -/

universe u

namespace Langlands.GroupScheme

/-- **A simply connected group has a closed simply connected quasi-split subgroup containing
its maximal split torus as a maximal split torus.** -/
theorem simplyConnectedQuasiSplitEnvelope : SimplyConnectedQuasiSplitEnvelopeStatement.{u} :=
  simplyConnectedQuasiSplitEnvelope_of_maximalSplitSubgroup
    maximalSplitSubgroup nonmultipliableCorootSpan

end Langlands.GroupScheme
