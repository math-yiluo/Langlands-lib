import Langlands.Shimura.Coefficients.ScalarRestriction
import Mathlib.CategoryTheory.Sites.Adjunction

/-! # Scalar restriction of constant-module associated sheaves -/

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C : Type w} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable [HasSheafify J (ModuleCat.{u} R)] [HasSheafify J (ModuleCat.{u} S)]

/-- Constant module sheaves commute with restriction of scalars. -/
def constantRestrictScalarsIso :
    constantSheaf J (ModuleCat.{u} S) ⋙ sheafCompose J (ModuleCat.restrictScalars.{u} φ) ≅
      ModuleCat.restrictScalars.{u} φ ⋙ constantSheaf J (ModuleCat.{u} R) :=
  constantCommuteCompose J (ModuleCat.restrictScalars.{u} φ)

variable {G : Type u} [Group G]

/-- The constant-sheaf restriction comparison preserves every group operator. -/
def constantActionRestrictScalarsIso :
    (constantSheaf J (ModuleCat.{u} S)).mapAction G ⋙
        (sheafCompose J (ModuleCat.restrictScalars.{u} φ)).mapAction G ≅
      (ModuleCat.restrictScalars.{u} φ).mapAction G ⋙
        (constantSheaf J (ModuleCat.{u} R)).mapAction G :=
  (Functor.mapActionComp G _ _).symm ≪≫
    Functor.mapActionCongr G (constantRestrictScalarsIso J φ) ≪≫
      Functor.mapActionComp G _ _

@[simp]
theorem constantActionRestrictScalarsIso_hom_hom (M : Action (ModuleCat.{u} S) G) :
    ((constantActionRestrictScalarsIso J φ).hom.app M).hom =
      (constantRestrictScalarsIso J φ).hom.app M.V := by
  simp [constantActionRestrictScalarsIso]

@[simp]
theorem constantActionRestrictScalarsIso_inv_hom (M : Action (ModuleCat.{u} S) G) :
    ((constantActionRestrictScalarsIso J φ).inv.app M).hom =
      (constantRestrictScalarsIso J φ).inv.app M.V := by
  simp [constantActionRestrictScalarsIso]

variable [HasBinaryProducts C] (Y : Action C G)

/-- Restricting scalars commutes with associated sheaves of constant modules. -/
def constantAssociatedRestrictScalarsIso :
    constantAssociatedFunctor J Y ⋙ sheafCompose J (ModuleCat.restrictScalars.{u} φ) ≅
      (ModuleCat.restrictScalars.{u} φ).mapAction G ⋙ constantAssociatedFunctor J Y :=
  Functor.isoWhiskerLeft ((constantSheaf J (ModuleCat.{u} S)).mapAction G)
      (associatedRestrictScalarsIso J φ Y) ≪≫
    Functor.isoWhiskerRight (constantActionRestrictScalarsIso J φ) (associatedFunctor J Y)

/-- The forward comparison is normalized by the actual invariant inclusion. -/
@[reassoc]
theorem constantAssociatedRestrictScalarsIso_hom_inclusion
    (M : Action (ModuleCat.{u} S) G) :
    (constantAssociatedRestrictScalarsIso J φ Y).hom.app M ≫
        inclusion J Y ((constantSheaf J (ModuleCat.{u} R)).mapAction G |>.obj
          ((ModuleCat.restrictScalars.{u} φ).mapAction G |>.obj M)) =
      (sheafCompose J (ModuleCat.restrictScalars.{u} φ)).map
          (inclusion J Y ((constantSheaf J (ModuleCat.{u} S)).mapAction G |>.obj M)) ≫
        (productSheaf J Y.V).map ((constantRestrictScalarsIso J φ).hom.app M.V) := by
  change ((associatedRestrictScalarsIso J φ Y).hom.app
      (((constantSheaf J (ModuleCat.{u} S)).mapAction G).obj M) ≫
      (associatedFunctor J Y).map ((constantActionRestrictScalarsIso J φ).hom.app M)) ≫ _ = _
  rw [Category.assoc]
  erw [inclusion_natural J Y ((constantActionRestrictScalarsIso J φ).hom.app M)]
  rw [← Category.assoc]
  erw [associatedRestrictScalarsIso_hom_inclusion J φ Y
    (((constantSheaf J (ModuleCat.{u} S)).mapAction G).obj M)]
  rw [constantActionRestrictScalarsIso_hom_hom]

/-- The inverse comparison has the corresponding invariant-inclusion normalization. -/
@[reassoc]
theorem constantAssociatedRestrictScalarsIso_inv_inclusion
    (M : Action (ModuleCat.{u} S) G) :
    (constantAssociatedRestrictScalarsIso J φ Y).inv.app M ≫
        (sheafCompose J (ModuleCat.restrictScalars.{u} φ)).map
          (inclusion J Y ((constantSheaf J (ModuleCat.{u} S)).mapAction G |>.obj M)) =
      inclusion J Y ((constantSheaf J (ModuleCat.{u} R)).mapAction G |>.obj
          ((ModuleCat.restrictScalars.{u} φ).mapAction G |>.obj M)) ≫
        (productSheaf J Y.V).map ((constantRestrictScalarsIso J φ).inv.app M.V) := by
  change ((associatedFunctor J Y).map ((constantActionRestrictScalarsIso J φ).inv.app M) ≫
      (associatedRestrictScalarsIso J φ Y).inv.app
        (((constantSheaf J (ModuleCat.{u} S)).mapAction G).obj M)) ≫ _ = _
  rw [Category.assoc]
  erw [associatedRestrictScalarsIso_inv_inclusion J φ Y
    (((constantSheaf J (ModuleCat.{u} S)).mapAction G).obj M)]
  erw [inclusion_natural J Y ((constantActionRestrictScalarsIso J φ).inv.app M)]
  rw [constantActionRestrictScalarsIso_inv_hom]
  rfl

end Langlands.Shimura.Coefficients
