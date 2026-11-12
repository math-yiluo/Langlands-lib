import Langlands.GroupScheme.Rational.FundamentalRepresentationsAssembly
import Langlands.GroupScheme.Rational.DominantHighestWeightProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity

/-!
# Existence of fundamental representations for simply connected split groups

Unconditional proof of `SplitFundamentalRepresentationsExistStatement`, obtained by applying
the conditional assembly `splitFundamentalRepresentationsExist_of_corootSpan_of_highestWeight`
to the published proofs of its two inputs.
-/

universe u

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, every actual simply connected group with a supplied
split pinning has a fundamental highest-weight representation at each simple root. -/
theorem splitFundamentalRepresentationsExist :
    SplitFundamentalRepresentationsExistStatement.{u} :=
  splitFundamentalRepresentationsExist_of_corootSpan_of_highestWeight
    splitSimplyConnectedCorootSpan splitDominantHighestWeightRepresentationsExist

end Langlands.GroupScheme
