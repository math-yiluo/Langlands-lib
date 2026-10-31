import Langlands.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
import Langlands.Representation.RankinSelberg.UnequalRankSourceAssembly
import Langlands.Representation.Whittaker.MirabolicFiniteLengthProof
import Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingProof
import Langlands.Representation.RankinSelberg.UnequalRankCompactGenericPairingProof

/-!
# Full Whittaker-type unequal-rank bilinear uniqueness

The three proved source inputs discharge the public finite-length assembly.
The resulting unconditional bound on the original carriers descends to every
specified pair of coefficient models.
-/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- Outside finitely many spectral values, the actual source-carrier
covariant form space of full Whittaker-type data has length at most one. -/
theorem unequalRankSourceLengthBound {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) :
    UnequalRankSourceLengthBoundStatement.{uF,uV,uW} F T n r :=
  UnequalRankAssembly.sourceLengthBound_of_statements F T n r
    Whittaker.mirabolicFiniteLength.{uF,uV}
    (unequalRankMirabolicPairingRigidity.{uF,uV,uW} F T n r)
    (unequalRankCompactGenericPairing.{uF,uW} F T n r)

/-- Full Whittaker-type unequal-rank bilinear uniqueness on the actual
coefficient models, outside a finite set of spectral values. -/
theorem unequalRankBilinearUniqueness {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) :
    UnequalRankBilinearUniquenessStatement.{uF,uV,uW} F T n r :=
  UnequalRankAssembly.unequalRankBilinearUniqueness_of_source_length F T n r
    (unequalRankSourceLengthBound.{uF,uV,uW} F T n r)

end Langlands.RankinSelberg
