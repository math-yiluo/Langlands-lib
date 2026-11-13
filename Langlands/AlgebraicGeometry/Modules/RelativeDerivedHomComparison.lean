import Langlands.Cohomology.DerivedSectionsHomComparison
import Langlands.AlgebraicGeometry.Modules.RelativeAbelianSheafCohomologyMap
import Langlands.AlgebraicGeometry.Modules.CanonicalPushforwardCohomology
import Langlands.Cohomology.AbelianSheafCohomologyPullback
import Langlands.Cohomology.HomologyDerivedFunctoriality

/-! # Relative derived sections and Hom from the constant integer sheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Opposite
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

/-- The specified relative sections are Hom from the actual integer sheaf. -/
def relativeSectionsHomIso (f : X.left ⟶ Spec R) :
    DerivedSections.relativeGlobalSections f ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      toAbSheaf X.left ⋙ preadditiveCoyoneda.obj
        (op (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat)) :=
  relativeGlobalSectionsForgetIso f ≪≫ (globalSectionsIso X.left).symm ≪≫
    isoWhiskerLeft (toAbSheaf X.left)
      (AbelianSheafDerivedSections.homGlobalSectionsIso X.left.toTopCat).symm

/-- The natural derived sections/Hom comparison for the actual underlying sheaf. -/
abbrev relativeDerivedHomComparison (f : X.left ⟶ Spec R) (n : ℤ) :=
  DerivedSectionsHomComparison.comparison.{u+1}
    (DerivedSections.relativeGlobalSections f)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (toAbSheaf X.left) (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat)
    (relativeSectionsHomIso f) n

/-- An injective module is acyclic for Hom from the actual integer sheaf. -/
lemma isZero_rightDerived_integerHom_of_injective (I : InjectiveObject X.left.Modules)
    (q : ℕ) : IsZero
      (((preadditiveCoyoneda.obj
        (op (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat))).rightDerived
          (q + 1)).obj ((toAbSheaf X.left).obj I.obj)) := by
  have : Injective I.obj := I.property
  exact (isZero_rightDerived_globalSections_of_injective X.left I.obj q).of_iso
    ((AbelianSheafDerivedSections.homRightDerivedIso X.left.toTopCat (q + 1)).app
      ((toAbSheaf X.left).obj I.obj))

instance relativeDerivedHomComparison_isIso (f : X.left ⟶ Spec R) (n : ℤ) :
    IsIso (relativeDerivedHomComparison f n) :=
  DerivedSectionsHomComparison.isIso_comparison.{u+1}
    (DerivedSections.relativeGlobalSections f)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (toAbSheaf X.left) (AbelianSheafDerivedSections.constantIntegers X.left.toTopCat)
    (relativeSectionsHomIso f) isZero_rightDerived_integerHom_of_injective n

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
