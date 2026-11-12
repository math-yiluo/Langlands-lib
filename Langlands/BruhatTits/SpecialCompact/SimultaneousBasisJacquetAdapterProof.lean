import Langlands.BruhatTits.SpecialCompact.JacquetAdapterProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # Proof of the actual simultaneous-basis Jacquet adapter -/

universe u

namespace Langlands.BruhatTits.SpecialCompact

/-- For every connected reductive group over a nonarchimedean local field, maximal
split torus, generic cocharacter and subgroup `K0`, the simultaneous standard basis
at `K0` supplies the existing Jacquet Iwahori-contraction predicate on the actual
standard radical, Levi and opposite radical of every standard parabolic. -/
theorem simultaneousBasisJacquetAdapter : SimultaneousBasisJacquetAdapterStatement.{u} :=
  simultaneousBasisJacquetAdapter_of_standardCocharacterStatement
    Langlands.GroupScheme.standardCocharacter

end Langlands.BruhatTits.SpecialCompact
