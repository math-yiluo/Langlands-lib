import Langlands.AlgebraicGeometry.Picard.TwoAxisClassRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.TwoAxisValuationClassSurjectivity
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassSectionExtension

/-! # Normal finite-type two-axis extension from class representability -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Representability of the two-axis class presheaf over noetherian affine bases implies
the normal finite-type two-axis extension property. -/
theorem normalFiniteTypeTwoAxisExtensionProperty_of_twoAxisClassRepresentability
    (hrep : NoetherianTwoAxisClassRepresentabilityStatement.{u}) :
    NormalFiniteTypeTwoAxisExtensionProperty.{u} := by
  intro T _ _ _ _ B
  dsimp only
  intro N h₁ h₂
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing ℤ T
  obtain ⟨Y, q, ⟨e⟩, hsep, hlft, hunr⟩ := hrep T B
  exact TwoAxisRigidifiedLineBundle.actualBundleExtension_of_normal_discreteValuativeExistence
    (CommRingCat.of T) (FractionRing T) B q e
    (TwoAxisRigidifiedLineBundle.discreteValuativeExistence_of_representableBy B q e) N h₁ h₂

end Langlands.AbelianScheme
