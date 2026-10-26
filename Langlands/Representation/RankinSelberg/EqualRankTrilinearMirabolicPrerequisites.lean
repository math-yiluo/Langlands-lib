import Langlands.Representation.RankinSelberg.EqualRankTrilinearPrerequisites
import Langlands.Representation.Classification.FiniteLengthProof

/-! Equal-rank assembly with the GL finite-length inputs discharged. -/

namespace Langlands.RankinSelberg

open Whittaker

universe uF uV uW

/-- The seven remaining inputs after applying the published GL finite-length proof. -/
def EqualRankTrilinearMirabolicPrerequisites
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  MirabolicFiniteLengthStatement.{uF,uV} ∧
  MirabolicFiniteLengthStatement.{uF,uW} ∧
  MirabolicFunctionalMultiplicityStatement.{uF,uV} F T n ∧
  MirabolicFunctionalMultiplicityStatement.{uF,uW} F T n ∧
  MirabolicTwistedPairingRigidityStatement.{uF,uV,uW} F T n ∧
  MirabolicCompactTwistedPairingStatement.{uF} F T n ∧
  EqualRankFrobeniusStatement.{uF,uV,uW} F T n

/-- The GL finite-length theorem supplies the two omitted premises. -/
theorem equalRankTrilinearPrerequisites_of_mirabolic
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (h : EqualRankTrilinearMirabolicPrerequisites.{uF,uV,uW} F T n) :
    EqualRankTrilinearPrerequisites.{uF,uV,uW} F T n :=
  ⟨glAdmissibleFiniteLength.{uF,uV}, glAdmissibleFiniteLength.{uF,uW}, h⟩

/-- Equal-rank uniqueness from the remaining mirabolic and Frobenius inputs. -/
theorem equalRankTrilinearUniqueness_of_mirabolic_prerequisites
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (h : EqualRankTrilinearMirabolicPrerequisites.{uF,uV,uW} F T n) :
    EqualRankTrilinearUniquenessStatement.{uF,uV,uW} F T n :=
  equalRankTrilinearUniqueness_of_prerequisites F T n
    (equalRankTrilinearPrerequisites_of_mirabolic F T n h)

end Langlands.RankinSelberg
