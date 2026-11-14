import Langlands.Representation.RankinSelberg.EqualRankTrilinearMirabolicPrerequisites
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Group.GL.UnramifiedCharacterSupplement
import Langlands.AllField.Representation.Classification.FiniteLengthProof
import Langlands.AllField.Representation.CuspidalSupport.CuspidalTensorStatement
import Langlands.AllField.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof
import Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.CuspidalSupport.JacquetSubquotientProof
import Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatementSupplement
import Langlands.AllField.Representation.CuspidalSupport.TotalConjugatingCountStatement
import Langlands.AllField.Representation.Geometric.GeometricLemmaStatement
import Langlands.AllField.Representation.Induction.SingleBlockSupplement
import Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement
import Langlands.AllField.Representation.RankinSelberg.EqualRankTrilinearPrerequisites
/-! Equal-rank assembly with the GL finite-length inputs discharged. -/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CentralBilinearVanishingStatement EqualRankAnalyticStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankTrilinearMirabolicPrerequisites EqualRankTrilinearPrerequisites EqualRankTrilinearUniquenessStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement centralBilinearVanishing centralSpectralElement centralSpectralElement_det_abs centralSpectralElement_mem_center determinantWeight_centralSpectralElement equalRankTrilinearPrerequisites_of_mirabolic equalRankTrilinearUniqueness_of_mirabolic_prerequisites equalRankTrilinearUniqueness_of_prerequisites inverseUniformizer_normalizedAbsoluteValue mirabolic_exists_exception_length_le_one mirabolic_pair_control_of_statements mirabolic_shift_length_bound normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.Whittaker hiding MirabolicCompactTwistedPairingStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement
open Langlands.AllField.Whittaker

universe uF uV uW

/-- The seven remaining inputs after applying the published GL finite-length proof. -/
def EqualRankTrilinearMirabolicPrerequisites
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  MirabolicFiniteLengthStatement.{uF,uV} ∧
  MirabolicFiniteLengthStatement.{uF,uW} ∧
  MirabolicFunctionalMultiplicityStatement.{uF,uV} F T n ∧
  MirabolicFunctionalMultiplicityStatement.{uF,uW} F T n ∧
  MirabolicTwistedPairingRigidityStatement.{uF,uV,uW} F T n ∧
  MirabolicCompactTwistedPairingStatement.{uF} F T n ∧
  EqualRankFrobeniusStatement.{uF,uV,uW} F T n

/-- The GL finite-length theorem supplies the two omitted premises. -/
theorem equalRankTrilinearPrerequisites_of_mirabolic
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    (h : EqualRankTrilinearMirabolicPrerequisites.{uF,uV,uW} F T n) :
    EqualRankTrilinearPrerequisites.{uF,uV,uW} F T n :=
  ⟨glAdmissibleFiniteLength.{uF,uV}, glAdmissibleFiniteLength.{uF,uW}, h⟩

/-- Equal-rank uniqueness from the remaining mirabolic and Frobenius inputs. -/
theorem equalRankTrilinearUniqueness_of_mirabolic_prerequisites
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    (h : EqualRankTrilinearMirabolicPrerequisites.{uF,uV,uW} F T n) :
    EqualRankTrilinearUniquenessStatement.{uF,uV,uW} F T n :=
  equalRankTrilinearUniqueness_of_prerequisites F T n
    (equalRankTrilinearPrerequisites_of_mirabolic F T n h)

end Langlands.AllField.RankinSelberg
