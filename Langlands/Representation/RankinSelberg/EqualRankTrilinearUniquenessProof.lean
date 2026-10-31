import Langlands.Representation.RankinSelberg.EqualRankTrilinearMirabolicPrerequisites
import Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof
import Langlands.Representation.Whittaker.MirabolicFiniteLengthProof
import Langlands.Representation.Whittaker.MirabolicCompactTwistedPairingProof
import Langlands.Representation.Whittaker.MirabolicFunctionalMultiplicityProof
import Langlands.Representation.Whittaker.MirabolicTwistedPairingRigidityProof

/-! JPSS Section 2.10: equal-rank uniqueness on the actual coefficient models. -/

namespace Langlands.RankinSelberg

open Whittaker

universe uF uV uW

/-- JPSS Section 2.10, Proposition: equal-rank twisted invariant trilinear
forms are unique up to scalar outside finitely many spectral values. -/
theorem equalRankTrilinearUniqueness
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    EqualRankTrilinearUniquenessStatement.{uF,uV,uW} F T n :=
  equalRankTrilinearUniqueness_of_mirabolic_prerequisites F T n
    ⟨mirabolicFiniteLength.{uF,uV}, mirabolicFiniteLength.{uF,uW},
      mirabolicFunctionalMultiplicity.{uF,uV} F T n,
      mirabolicFunctionalMultiplicity.{uF,uW} F T n,
      mirabolicTwistedPairingRigidity.{uF,uV,uW} F T n,
      mirabolicCompactTwistedPairing.{uF} F T n, equalRankFrobenius.{uF,uV,uW} F T n⟩

end Langlands.RankinSelberg
