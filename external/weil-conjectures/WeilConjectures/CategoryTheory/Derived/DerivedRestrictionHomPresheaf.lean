/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedMorphismPresheaf
public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Restriction of coefficients on local derived Hom presheaves

Source: Stacks Project, Tags 03DA and 098K, restriction and localization of coefficients.
(blueprint: def-weil-pbc-restriction-hom-presheaf).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {B B' : Type (u + 1)}
  [CommRing B] [CommRing B'] (φ : B →+* B')

private noncomputable def mapScalarsSheafIso {U V : C} (f : V ⟶ U) :
    Sheaf.restrictScalars (J.over U) φ ⋙ J.overMapPullback (ModuleCat.{u + 1} B) f ≅
      J.overMapPullback (ModuleCat.{u + 1} B') f ⋙
        Sheaf.restrictScalars (J.over V) φ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private noncomputable def mapScalarsIso {U V : C} (f : V ⟶ U) :
    Sheaf.derivedRestrictScalars (J.over U) φ ⋙ derivedSliceMap J B f ≅
      derivedSliceMap J B' f ⋙ Sheaf.derivedRestrictScalars (J.over V) φ :=
  Functor.mapDerivedCategorySquareIso (mapScalarsSheafIso J φ f)

private theorem restriction_scalars_paste {U V : C} (f : V ⟶ U)
    (A : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B'))) :
    (sliceRestrictScalarsIso J B φ V).inv.app A ≫
        (Sheaf.derivedRestrictScalars (J.over V) φ).map
          ((derivedSliceMapIso J B' f).inv.app A) =
      (derivedSliceMapIso J B f).inv.app
          ((Sheaf.derivedRestrictScalars J φ).obj A) ≫
        (derivedSliceMap J B f).map ((sliceRestrictScalarsIso J B φ U).inv.app A) ≫
        (mapScalarsIso J φ f).hom.app ((derivedSliceRestriction J B' U).obj A) := by
  have h := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (sliceRestrictScalarsSheafIso J B φ U).symm
    (mapScalarsSheafIso J φ f)
    (sliceRestrictScalarsSheafIso J B φ V).symm
    (sliceRestrictionMapIso J B f).symm
    (sliceRestrictionMapIso J B' f).symm
    (fun M ↦ by ext W x; rfl) A
  simpa only [sliceRestrictScalarsIso, mapScalarsIso, derivedSliceMapIso,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc] using h

/-- Coefficient restriction commutes with restriction along a map of site objects.
Source: Stacks Tags 03DA and 098K.
(blueprint: def-weil-pbc-restriction-hom-presheaf).
Proof: paste the identity coefficient squares with the localization comparisons and
apply the derived-square pasting theorem. Naturality of the resulting square, followed
by cancellation of the localization isomorphisms, gives the equality. -/
theorem derivedRestrictionHomPresheaf_natural
    (A D : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B')))
    {U V : C} (f : V ⟶ U)
    (g : (derivedSliceRestriction J B' U).obj A ⟶
      (derivedSliceRestriction J B' U).obj D) :
    (sliceRestrictScalarsIso J B φ V).inv.app A ≫
        (normalizationRestrict (J.over V) φ).map
          (derivedLocalHomRestriction J B' A D f g) ≫
        (sliceRestrictScalarsIso J B φ V).hom.app D =
      derivedLocalHomRestriction J B
        ((normalizationRestrict J φ).obj A) ((normalizationRestrict J φ).obj D) f
        ((sliceRestrictScalarsIso J B φ U).inv.app A ≫
          (normalizationRestrict (J.over U) φ).map g ≫
          (sliceRestrictScalarsIso J B φ U).hom.app D) := by
  let R := normalizationRestrict (J.over V) φ
  let T := derivedSliceMap J B f
  let a := sliceRestrictScalarsIso J B φ V
  let b := sliceRestrictScalarsIso J B φ U
  let c := derivedSliceMapIso J B f
  let d := derivedSliceMapIso J B' f
  let e := mapScalarsIso J φ f
  have hA := restriction_scalars_paste J φ f A
  have hD := restriction_scalars_paste J φ f D
  change a.inv.app A ≫ R.map (d.inv.app A) =
    c.inv.app _ ≫ T.map (b.inv.app A) ≫ e.hom.app _ at hA
  change a.inv.app D ≫ R.map (d.inv.app D) =
    c.inv.app _ ≫ T.map (b.inv.app D) ≫ e.hom.app _ at hD
  change a.inv.app A ≫ R.map (d.inv.app A ≫ _ ≫ d.hom.app D) ≫ a.hom.app D =
    c.inv.app _ ≫ T.map (b.inv.app A ≫ _ ≫ b.hom.app D) ≫ c.hom.app _
  apply (cancel_mono (a.inv.app D ≫ R.map (d.inv.app D))).mp
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc,
    (R.mapIso (d.app D)).hom_inv_id_assoc]
  rw [hD]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc,
    (T.mapIso (b.app D)).hom_inv_id_assoc]
  rw [reassoc_of% hA]
  have hn := e.hom.naturality g
  dsimp only [Functor.comp_map] at hn
  have hd : R.map (d.hom.app D) ≫ R.map (d.inv.app D) = 𝟙 _ := by
    rw [← R.map_comp, Iso.hom_inv_id_app, R.map_id]
  have hb : T.map (b.hom.app D) ≫ T.map (b.inv.app D) = 𝟙 _ := by
    rw [← T.map_comp, Iso.hom_inv_id_app, T.map_id]
  simp only [hd, hb, reassoc_of% hb, Category.comp_id, Category.id_comp]
  exact congrArg (fun k ↦ c.inv.app _ ≫ T.map (b.inv.app A) ≫ k) hn.symm

/-- Restriction of coefficients on actual local derived Hom presheaves, transported by
canonical localization isomorphisms. Source: Stacks Tags 03DA and 098K.
(blueprint: def-weil-pbc-restriction-hom-presheaf). -/
def derivedRestrictionHomPresheaf
    (A D : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B'))) :
    derivedLocalHomPresheaf J B' A D ⟶
      derivedLocalHomPresheaf J B
        ((normalizationRestrict J φ).obj A) ((normalizationRestrict J φ).obj D) where
  app U := TypeCat.ofHom fun g ↦ (sliceRestrictScalarsIso J B φ U.unop).inv.app A ≫
    (normalizationRestrict (J.over U.unop) φ).map g ≫
      (sliceRestrictScalarsIso J B φ U.unop).hom.app D
  naturality := by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro g
    exact derivedRestrictionHomPresheaf_natural J φ A D f.unop g

end CategoryTheory
