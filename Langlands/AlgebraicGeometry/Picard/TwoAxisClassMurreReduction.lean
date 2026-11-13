import Langlands.AlgebraicGeometry.Picard.TwoAxisClassMurreConditionsStatement
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassRepresentabilityStatement

/-! # Representability of the two-axis class presheaf from Murre's criterion -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Murre's criterion, taken for presheaves valued in `Type (u + 1)`, together with Murre's
conditions for the two-axis class presheaf, gives its representability over noetherian
affine bases. -/
theorem noetherianTwoAxisClassRepresentability_of_murre
    (hM : UnramifiedFunctor.MurreCriterionStatement.{u, u + 1})
    (hSmallValues : NoetherianTwoAxisClassSmallValuesStatement.{u})
    (hZariskiSheaf : NoetherianTwoAxisClassZariskiSheafStatement.{u})
    (hFaithfullyFlatSheaf : NoetherianTwoAxisClassFaithfullyFlatSheafStatement.{u})
    (hFilteredColimits : NoetherianTwoAxisClassFilteredColimitsStatement.{u})
    (hAdicLimits : NoetherianTwoAxisClassAdicLimitsStatement.{u})
    (hArtinianLifting : NoetherianTwoAxisClassArtinianLiftingStatement.{u})
    (hNilpotentInjective : NoetherianTwoAxisClassNilpotentInjectiveStatement.{u})
    (hValuativeSeparation : NoetherianTwoAxisClassValuativeSeparationStatement.{u})
    (hOneDimensionalLifting : NoetherianTwoAxisClassOneDimensionalLiftingStatement.{u})
    (hGenericNonLifting : NoetherianTwoAxisClassGenericNonLiftingStatement.{u}) :
    NoetherianTwoAxisClassRepresentabilityStatement.{u} := by
  intro R _ _ A
  exact hM (Spec (CommRingCat.of R)) (TwoAxisRigidifiedLineBundle.classPresheaf A)
    (hSmallValues R A) (hZariskiSheaf R A) (hFaithfullyFlatSheaf R A)
    (hFilteredColimits R A) (hAdicLimits R A) (hArtinianLifting R A)
    (hNilpotentInjective R A) (hValuativeSeparation R A) (hOneDimensionalLifting R A)
    (hGenericNonLifting R A)

/-- The same reduction from the bundled conditions statement. -/
theorem noetherianTwoAxisClassRepresentability_of_murreConditions
    (hM : UnramifiedFunctor.MurreCriterionStatement.{u, u + 1})
    (h : NoetherianTwoAxisClassMurreConditionsStatement.{u}) :
    NoetherianTwoAxisClassRepresentabilityStatement.{u} :=
  noetherianTwoAxisClassRepresentability_of_murre hM h.1 h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2

end Langlands.AlgebraicGeometry.Picard
