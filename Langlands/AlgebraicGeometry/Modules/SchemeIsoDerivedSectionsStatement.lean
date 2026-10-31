import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.Cohomology.DerivedPlus

/-! # Actual derived sections under a scheme isomorphism -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

/-- Pullback by a scheme isomorphism preserves actual derived relative sections,
naturally in every module coefficient. -/
def SchemeIsoDerivedSectionsStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (X Y : Scheme.{u}) (e : X ≅ Y)
    (g : Y ⟶ Spec R),
    Nonempty
      (Scheme.Modules.pullback e.hom ⋙
          (Langlands.Cohomology.DerivedPlus.derivedComplex
              (DerivedSections.relativeGlobalSections (e.hom ≫ g)) ⋙
            DerivedCategory.Plus.ι) ≅
        Langlands.Cohomology.DerivedPlus.derivedComplex
            (DerivedSections.relativeGlobalSections g) ⋙
          DerivedCategory.Plus.ι)

end Langlands.AlgebraicGeometry.Modules
