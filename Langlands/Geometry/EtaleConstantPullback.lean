import Langlands.Geometry.EtaleRestrictionRightAdjoint
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Constant sheaves and etale restriction -/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory AlgebraicGeometry Opposite

universe u vA uA

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
variable (A : Type uA) [Category.{vA} A]
variable [HasWeakSheafify X.smallEtaleTopology A] [HasWeakSheafify Y.smallEtaleTopology A]

/-- Constant sheaves commute with restriction along an etale scheme morphism. -/
def constantPullbackIso :
    constantSheaf X.smallEtaleTopology A ⋙ restriction f A ≅
      constantSheaf Y.smallEtaleTopology A :=
  Functor.isoWhiskerLeft (Functor.const X.Etaleᵒᵖ)
    ((siteMap f).pushforwardContinuousSheafificationCompatibility A
      Y.smallEtaleTopology X.smallEtaleTopology).symm ≪≫
    Functor.isoWhiskerRight (Functor.constCompWhiskeringLeftIso Y.Etaleᵒᵖ (siteMap f).op)
      (presheafToSheaf Y.smallEtaleTopology A)

/-- The comparison carries the restricted constant-presheaf unit to the new unit. -/
@[reassoc] theorem constantPullbackIso_hom_unit (M : A) :
    Functor.whiskerLeft (siteMap f).op
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)) ≫
      ((constantPullbackIso f A).hom.app M).hom =
    toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M) := by
  let e := (siteMap f).pushforwardContinuousSheafificationCompatibility A
    Y.smallEtaleTopology X.smallEtaleTopology
  let c := (Functor.constCompWhiskeringLeftIso Y.Etaleᵒᵖ (siteMap f).op).hom.app M
  have h := (siteMap f).toSheafify_pullbackSheafificationCompatibility A
    Y.smallEtaleTopology X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)
  change Functor.whiskerLeft (siteMap f).op (toSheafify X.smallEtaleTopology _) ≫
    ((e.inv.app _).hom ≫ ((presheafToSheaf Y.smallEtaleTopology A).map c).hom) = _
  rw [← h, Category.assoc]
  erw [← ObjectProperty.FullSubcategory.comp_hom_assoc, Iso.hom_inv_id_app]
  erw [Category.id_comp]
  rw [← toSheafify_naturality]
  apply NatTrans.ext
  funext U
  exact Category.id_comp _

/-- The inverse comparison is the sheafification lift of the restricted unit. -/
@[reassoc] theorem constantPullbackIso_inv_unit (M : A) :
    toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M) ≫
      ((constantPullbackIso f A).inv.app M).hom =
    Functor.whiskerLeft (siteMap f).op
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)) := by
  apply (cancel_mono ((constantPullbackIso f A).hom.app M).hom).1
  rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact (constantPullbackIso_hom_unit f A M).symm

/-- Maps out of a restricted constant sheaf are determined on constant presheaves. -/
theorem constantPullback_hom_ext (M : A) {F : Sheaf Y.smallEtaleTopology A}
    (a b : (restriction f A).obj ((constantSheaf X.smallEtaleTopology A).obj M) ⟶ F)
    (h : Functor.whiskerLeft (siteMap f).op
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)) ≫ a.hom =
      Functor.whiskerLeft (siteMap f).op
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)) ≫ b.hom) : a = b := by
  apply (cancel_epi ((constantPullbackIso f A).inv.app M)).1
  apply Sheaf.hom_ext
  apply sheafify_hom_ext Y.smallEtaleTopology _ _ F.property
  change toSheafify Y.smallEtaleTopology _ ≫
      ((constantPullbackIso f A).inv.app M).hom ≫ a.hom =
    toSheafify Y.smallEtaleTopology _ ≫
      ((constantPullbackIso f A).inv.app M).hom ≫ b.hom
  simpa only [← Category.assoc, constantPullbackIso_inv_unit] using h

/-- The comparison respects restriction along the identity scheme morphism. -/
theorem constantPullbackIso_id (M : A) :
    (constantPullbackIso (𝟙 X) A).hom.app M =
      (restrictionId A).hom.app ((constantSheaf X.smallEtaleTopology A).obj M) := by
  apply constantPullback_hom_ext (𝟙 X) A M
  rw [constantPullbackIso_hom_unit]
  apply NatTrans.ext
  funext U
  dsimp [restrictionId]
  simp only [Category.comp_id]
  have h := (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).naturality
    (((MorphismProperty.Over.mapId ⊤ X).inv.app U.unop).op)
  change 𝟙 M ≫ _ = _ at h
  rw [Category.id_comp] at h
  exact h

/-- The comparison respects successive etale base morphisms. -/
theorem constantPullbackIso_comp {Z : Scheme.{u}} (g : Z ⟶ Y) [Etale g]
    [HasWeakSheafify Z.smallEtaleTopology A] (M : A) :
    (restrictionComp f A g).hom.app ((constantSheaf X.smallEtaleTopology A).obj M) ≫
        (constantPullbackIso (g ≫ f) A).hom.app M =
      (restriction g A).map ((constantPullbackIso f A).hom.app M) ≫
        (constantPullbackIso g A).hom.app M := by
  apply (cancel_epi ((restrictionComp f A g).inv.app
    ((constantSheaf X.smallEtaleTopology A).obj M))).1
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply constantPullback_hom_ext (g ≫ f) A M
  rw [constantPullbackIso_hom_unit]
  have h : Functor.whiskerLeft (siteMap (g ≫ f)).op
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)) ≫
      ((restrictionComp f A g).inv.app
        ((constantSheaf X.smallEtaleTopology A).obj M)).hom =
    Functor.whiskerLeft (siteMap g).op
      (Functor.whiskerLeft (siteMap f).op
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M))) := by
    apply NatTrans.ext
    funext U
    dsimp [restrictionComp]
    have h := (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).naturality
      (((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale g)
        (inferInstance : Etale f)).inv.app U.unop).op)
    change 𝟙 M ≫ _ = _ at h
    rw [Category.id_comp] at h
    exact h.symm
  change _ = _ ≫ ((restrictionComp f A g).inv.app _).hom ≫
    (Functor.whiskerLeft (siteMap g).op ((constantPullbackIso f A).hom.app M).hom) ≫
      ((constantPullbackIso g A).hom.app M).hom
  rw [← Category.assoc, h, ← Functor.whiskerLeft_comp_assoc,
    constantPullbackIso_hom_unit, constantPullbackIso_hom_unit]

end Langlands.Geometry.EtalePullback
