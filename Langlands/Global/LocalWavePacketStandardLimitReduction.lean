import Langlands.Global.LocalWavePacketStandardReduction
import Langlands.Global.AdelicTruncatedEisensteinUniformAsymptoticsStatement
import Langlands.Global.LocalWavePacketMainTermLimitStatement
import Langlands.Global.AdelicEisensteinPointwiseContinuationStatement
import Langlands.Global.AdelicEisensteinJointRootHyperplaneStatement
import Langlands.Global.AdelicIntertwiningSquareIntegrableExpansionStatement

/-! # Lapid's §8 limit for standard parabolic subgroups from Proposition 1 and the main-term limit

Lapid 2011, §8, p.328: the Fourier transform on `𝔞_G` writes the truncated inner product of two
wave packets as an integral of truncated inner products of Eisenstein series on
`G(F) \ G(𝔸)¹`; Proposition 1, uniformly in the central parameter, replaces these by the main
terms of formula (2) up to an exponentially small error; and the integral (18) of the main terms
tends to the right side of formula (4).

* `TruncatedStandardWavePacketLimitReductionStatement`: the implication from Proposition 1 in
  the form `LocalTruncatedEisensteinFamilyUniformInnerProductStatement`, the main-term limit
  `WavePacketMainTermLimitStatement`, and the Library's statements on the continuation of
  Eisenstein series and on expansions of intertwining operators, to
  `TruncatedStandardWavePacketLimitStatement`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global

/-- Lapid 2011, §8, p.328, the passage from Proposition 1 and the limit of (18) to the limit of
truncated inner products of wave packets, for standard parabolic subgroups. -/
def TruncatedStandardWavePacketLimitReductionStatement : Prop :=
  LocalTruncatedEisensteinFamilyUniformInnerProductStatement →
  WavePacketMainTermLimitStatement →
  EisensteinPointwiseContinuationStatement.{0} →
  EisensteinJointRootHyperplaneStatement.{0} →
  IntertwiningSquareIntegrableExpansionStatement →
  TruncatedStandardWavePacketLimitStatement

end Langlands.Global
