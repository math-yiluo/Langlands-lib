import Langlands.Representation.Aubert.General.RationalContragredientWeylReduction
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.GroupScheme.Rational.StandardLeviConjugationProof
import Langlands.GroupScheme.Rational.StandardAssociatedOppositeTransportProof
import Langlands.Representation.Aubert.General.RationalInductionDualityProof
import Langlands.Representation.Aubert.General.RationalJacquetDualityProof

/-! # Rational contragredient commutation from the remaining representation inputs -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- The remaining representation-theoretic prerequisites imply the unchanged
closed commutation target. The three antecedents are separate proof obligations. -/
def RationalContragredientAssemblyStatement : Prop :=
  RationalPointsFiniteLengthAdmissibleStatement.{u, max (u + 1) v} →
    DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v} →
      RationalInducedClassWeylConjugacyStatement.{u, v} →
        RationalContragredientCommutationStatement.{u, v}

/-- Discharge the structural transport and natural-duality inputs by their
published proofs, retaining precisely the three representation prerequisites. -/
theorem rationalContragredientCommutation_of_admissibility_and_inducedWeyl :
    RationalContragredientAssemblyStatement.{u, v} := by
  intro hadmG hadmM hWeyl
  exact rationalContragredientCommutation_of_schemeWeylDuality
    GroupScheme.relativeWeylCoxeter
    GroupScheme.standardLeviConjugation
    GroupScheme.standardAssociatedOppositeTransport
    hWeyl rationalNaturalInductionDuality rationalNaturalJacquetDuality hadmG hadmM

end Langlands.Aubert.General.RationalPointFamily
