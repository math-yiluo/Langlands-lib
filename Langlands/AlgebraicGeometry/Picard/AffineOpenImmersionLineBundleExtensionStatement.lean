import Langlands.AlgebraicGeometry.Picard.OpenImmersionLineBundleExtensionStatement

/-! # The affine-target case of open-immersion line-bundle extension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- The affine-target case of general line-bundle extension, with factoriality
only at points outside the open range. This defines the proposition. -/
def AffineOpenImmersionLineBundleExtensionStatement : Prop :=
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsAffine X]
    (Y : Scheme.{u}) (j : Y ⟶ X) [IsOpenImmersion j],
    (∀ x : X, x ∉ Set.range j →
      UniqueFactorizationMonoid (X.presheaf.stalk x)) →
    ∀ (D : LineBundle Y),
      ∃ (E : LineBundle X),
        Nonempty (((LineBundle.pullback j).obj E).obj ≅ D.obj)

end Langlands.AlgebraicGeometry.Picard
