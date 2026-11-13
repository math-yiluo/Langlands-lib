import Langlands.Representation.RankinSelberg.UnequalRankBilinearUniquenessProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactGenericPairingProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicPairingProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankSourceAssembly
import Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthProof
/-!
# Full Whittaker-type unequal-rank bilinear uniqueness

The three proved source inputs discharge the public finite-length assembly.
The resulting unconditional bound on the original carriers descends to every
specified pair of coefficient models.
-/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement UnequalRankCompactGenericPairingStatement UnequalRankFunctionalEquationStatement UnequalRankMirabolicPairingRigidityStatement UnequalRankSourceLengthBoundStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankBilinearUniqueness unequalRankCompactGenericPairing unequalRankMirabolicPairingRigidity unequalRankSourceLengthBound
open Langlands.AllField.RankinSelberg

universe uF uV uW

/-- Outside finitely many spectral values, the actual source-carrier
covariant form space of full Whittaker-type data has length at most one. -/
theorem unequalRankSourceLengthBound 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ) :
    UnequalRankSourceLengthBoundStatement.{uF,uV,uW} F T n r :=
  Langlands.AllField.RankinSelberg.UnequalRankAssembly.sourceLengthBound_of_statements F T n r
    Langlands.AllField.Whittaker.mirabolicFiniteLength.{uF,uV}
    (unequalRankMirabolicPairingRigidity.{uF,uV,uW} F T n r)
    (unequalRankCompactGenericPairing.{uF,uW} F T n r)

/-- Full Whittaker-type unequal-rank bilinear uniqueness on the actual
coefficient models, outside a finite set of spectral values. -/
theorem unequalRankBilinearUniqueness 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ) :
    UnequalRankBilinearUniquenessStatement.{uF,uV,uW} F T n r :=
  Langlands.AllField.RankinSelberg.UnequalRankAssembly.unequalRankBilinearUniqueness_of_source_length F T n r
    (unequalRankSourceLengthBound.{uF,uV,uW} F T n r)

end Langlands.AllField.RankinSelberg
