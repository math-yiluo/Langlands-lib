import Langlands.Representation.Aubert.General.RationalJacquetCartanDatum
import Langlands.BruhatTits.SpecialCompact.JointBasisProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof

/-!
# Jacquet–Cartan data on the rational points of reductive groups: proof

The rational points `G(F)` of every connected reductive group `G` over every
nonarchimedean local field `F`, with the point topology, carry a
`Langlands.JacquetCartanDatum` (`RationalPointsJacquetCartanDatumStatement`).
The proof applies `rationalPointsJacquetCartanDatum_of` to the proved joint
special compact basis existence, standard cocharacter and standard parabolic
order statements.
-/

universe u

namespace Langlands.Aubert.General

/-- **Jacquet–Cartan data on `G(F)`.** For every nonarchimedean local field `F`
and every connected reductive group `G` over `F`, the rational points `G(F)`,
with the topology `rationalPointTopology F G.X`, carry a Jacquet–Cartan datum
whose index and wall types lie in the universe `u` of `F` (Renard V.5.1, V.5.2
and the proof of VI.2.1). -/
theorem rationalPointsJacquetCartanDatum : RationalPointsJacquetCartanDatumStatement.{u} :=
  rationalPointsJacquetCartanDatum_of
    Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence
    Langlands.GroupScheme.standardCocharacter
    Langlands.GroupScheme.standardParabolicOrder

end Langlands.Aubert.General
