/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Derived morphism presheaves on localized sites

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
section ExactFunctors

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private noncomputable def exactComp (e : H ≅ F ⋙ G) :
    H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm

@[reassoc]
private lemma exactComp_fac (e : H ≅ F ⋙ G)
    (P : HomotopyCategory C (.up ℤ)) :
    (exactComp F G H e).hom.app (DerivedCategory.Qh.obj P) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app P) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj P) =
    H.mapDerivedCategoryFactorsh.hom.app P ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) := by
  have hcomp := Functor.mapDerivedCategoryCompIso_fach F G P
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at hcomp
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hcomp
  simp only [exactComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [hcomp, Functor.mapDerivedCategoryNatIso_fach]

end ExactFunctors

section ExactAssociativity

variable {C₀ C₁ C₂ C₃ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  (H : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (F : C₂ ⥤ C₃)
  (GH : C₀ ⥤ C₂) (FG : C₁ ⥤ C₃) (FGH : C₀ ⥤ C₃)
  [H.Additive] [G.Additive] [F.Additive] [GH.Additive] [FG.Additive] [FGH.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
  [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
  [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]

private lemma exactComp_assoc
    (e : GH ≅ H ⋙ G) (d : FG ≅ G ⋙ F)
    (a : FGH ≅ GH ⋙ F) (b : FGH ≅ H ⋙ FG)
    (hcoh : a.hom ≫ Functor.whiskerRight e.hom F =
      b.hom ≫ Functor.whiskerLeft H d.hom) :
    (exactComp GH F FGH a).hom ≫
      Functor.whiskerRight (exactComp H G GH e).hom F.mapDerivedCategory =
    (exactComp H FG FGH b).hom ≫
      Functor.whiskerLeft H.mapDerivedCategory (exactComp G F FG d).hom := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (.up ℤ)) (fun P => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (F.mapDerivedCategory.map
      (G.mapDerivedCategory.map
        (H.mapDerivedCategoryFactorsh.hom.app P)) ≫
    F.mapDerivedCategory.map
      (G.mapDerivedCategoryFactorsh.hom.app
        ((H.mapHomotopyCategory (.up ℤ)).obj P)) ≫
    F.mapDerivedCategoryFactorsh.hom.app
      ((G.mapHomotopyCategory (.up ℤ)).obj
        ((H.mapHomotopyCategory (.up ℤ)).obj P)))]
  have u₁ := exactComp_fac H G GH e P
  have u₂ := exactComp_fac GH F FGH a P
  have u₃ := exactComp_fac G F FG d
    ((H.mapHomotopyCategory (.up ℤ)).obj P)
  have u₄ := exactComp_fac H FG FGH b P
  have n₁ := F.mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory
      e.hom (.up ℤ)).app P)
  have n₂ := (exactComp G F FG d).hom.naturality
    (H.mapDerivedCategoryFactorsh.hom.app P)
  simp only [Functor.comp_map, Functor.comp_obj] at n₁ n₂
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  erw [u₁, Functor.map_comp_assoc, n₁,
    reassoc_of% u₂, ← reassoc_of% n₂, u₃, reassoc_of% u₄,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  congr 1
  obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  change (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map _ =
    (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 1
  exact NatTrans.congr_app hcoh (Q.X n)

end ExactAssociativity

private lemma conjugate_id {C : Type*} [Category C]
    (F : C ⥤ C) (e : F ≅ 𝟭 C) {X Y : C}
    (p : X ≅ F.obj X) (q : Y ≅ F.obj Y)
    (hp : p.hom ≫ e.hom.app X = 𝟙 X) (hq : q.hom ≫ e.hom.app Y = 𝟙 Y)
    (a : X ⟶ Y) : p.hom ≫ F.map a ≫ q.inv = a := by
  have he : q.inv = e.hom.app Y := by
    rw [← cancel_epi q.hom, Iso.hom_inv_id, hq]
  have hn := e.hom.naturality a
  simp only [Functor.id_map] at hn
  rw [he, hn, ← Category.assoc, hp, Category.id_comp]

private lemma conjugate_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : D ⥤ E) (G : C ⥤ D) (H : C ⥤ E) (e : H ≅ G ⋙ F)
    {K L : C} {P Q : D} {A B : E}
    (p : A ≅ F.obj P) (q : P ≅ G.obj K) (r : A ≅ H.obj K)
    (p' : B ≅ F.obj Q) (q' : Q ≅ G.obj L) (r' : B ≅ H.obj L)
    (hK : p.hom ≫ F.map q.hom = r.hom ≫ e.hom.app K)
    (hL : p'.hom ≫ F.map q'.hom = r'.hom ≫ e.hom.app L) (a : K ⟶ L) :
    r.hom ≫ H.map a ≫ r'.inv =
      p.hom ≫ F.map (q.hom ≫ G.map a ≫ q'.inv) ≫ p'.inv := by
  rw [← cancel_mono (p'.hom ≫ F.map q'.hom)]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hL, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [e.hom.naturality, ← Category.assoc, ← hK, Category.assoc]
  rfl

section ExactIdentity

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) (J : D ⥤ D)
  [F.Additive] [J.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]

private noncomputable def exactId (j : J ≅ 𝟭 D) :
    J.mapDerivedCategory ≅ 𝟭 (DerivedCategory D) :=
  Functor.mapDerivedCategoryNatIso j ≪≫ Functor.mapDerivedCategoryIdIso D

private lemma exactId_fac (j : J ≅ 𝟭 D) (P : HomotopyCategory D (.up ℤ)) :
    (exactId J j).hom.app (DerivedCategory.Qh.obj P) =
      J.mapDerivedCategoryFactorsh.hom.app P ≫ DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory j.hom (.up ℤ)).app P ≫
          (Functor.mapHomotopyCategoryIdIso D (.up ℤ)).hom.app P) := by
  have hid := NatTrans.congr_app (congrArg Iso.hom
    (Functor.mapDerivedCategoryIdIso_factorsh D)) P
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hid
  erw [Category.comp_id, Category.comp_id] at hid
  simp only [exactId, Iso.trans_hom, NatTrans.comp_app, hid, Functor.map_comp]
  rw [Functor.mapDerivedCategoryNatIso_fach_assoc]

private lemma exactComp_unit (j : J ≅ 𝟭 D) (e : F ≅ F ⋙ J)
    (hcoh : e.hom ≫ Functor.whiskerLeft F j.hom = F.rightUnitor.inv) :
    (exactComp F J F e).hom ≫
      Functor.whiskerLeft F.mapDerivedCategory (exactId J j).hom =
        F.mapDerivedCategory.rightUnitor.inv := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (.up ℤ)) (fun P => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app]
  have hn := (exactId J j).hom.naturality (F.mapDerivedCategoryFactorsh.hom.app P)
  simp only [Functor.id_map, Functor.comp_obj] at hn
  rw [← cancel_mono (F.mapDerivedCategoryFactorsh.hom.app P),
    Category.assoc, ← hn, exactId_fac, exactComp_fac_assoc]
  rw [← Functor.map_comp]
  have hu : (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P ≫
      (NatTrans.mapHomotopyCategory j.hom (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
      (Functor.mapHomotopyCategoryIdIso D (.up ℤ)).hom.app
        ((F.mapHomotopyCategory (.up ℤ)).obj P) = 𝟙 _ := by
    rw [Functor.mapHomotopyCategoryIdIso_hom_app_eq_id]
    erw [Category.comp_id]
    obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    change (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map _ = 𝟙 _
    rw [← Functor.map_comp, ← (HomotopyCategory.quotient _ (.up ℤ)).map_id]
    congr 1
    ext n : 1
    exact NatTrans.congr_app hcoh (Q.X n)
  erw [hu, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

end ExactIdentity

namespace CategoryTheory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
variable (J : GrothendieckTopology C) (B : Type (u + 1)) [CommRing B]

/-- Restriction of module sheaves to the localized site is additive, section by section.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
instance derivedSliceRestriction_additive (U : C) :
    (J.overPullback (ModuleCat.{u + 1} B) U).Additive where
  map_add := by intros; rfl

/-- Relocalization along a map of site objects is additive, section by section.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
instance derivedSliceMap_additive {U V : C} (f : V ⟶ U) :
    (J.overMapPullback (ModuleCat.{u + 1} B) f).Additive where
  map_add := by intros; rfl

/-- Exact restriction to a localized site, applied to the actual derived category.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev derivedSliceRestriction (U : C) :=
  (J.overPullback (ModuleCat.{u + 1} B) U).mapDerivedCategory

omit [EssentiallySmall.{u + 1} C] in
/-- Relocalization is exact: in particular it preserves finite colimits.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves)

Proof: Relocalization is inverse image for localization of topoi. Its restriction description is
left exact. It is also a left adjoint (the localized-site restriction adjunction), hence
preserves colimits. Apply this to constant-coefficient module sheaves; finite colimits are among
these colimits. -/
theorem derivedSliceMap_preservesFiniteColimits {U V : C} (f : V ⟶ U) :
    PreservesFiniteColimits (J.overMapPullback (ModuleCat.{u + 1} B) f) := by
  have : PreservesColimitsOfSize.{0, 0}
      (J.overMapPullback (ModuleCat.{u + 1} B) f) :=
    ((Over.map f).sheafAdjunctionCocontinuous
    (ModuleCat.{u + 1} B) (J.over V) (J.over U)).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

attribute [instance] derivedSliceMap_preservesFiniteColimits

/-- Exact relocalization of derived module sheaves along a map of site objects.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev derivedSliceMap {U V : C} (f : V ⟶ U) :=
  (J.overMapPullback (ModuleCat.{u + 1} B) f).mapDerivedCategory

/-- The canonical restriction/relocalization isomorphism on module sheaves.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def sliceRestrictionMapIso {U V : C} (f : V ⟶ U) :
    J.overPullback (ModuleCat.{u + 1} B) U ⋙
      J.overMapPullback (ModuleCat.{u + 1} B) f ≅
        J.overPullback (ModuleCat.{u + 1} B) V :=
  NatIso.ofComponents (fun F ↦ F.pushforwardOverMapIso f)
    (by intros; ext; rfl)

/-- The restriction/relocalization isomorphism induced on derived categories.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedSliceMapIso {U V : C} (f : V ⟶ U) :
    derivedSliceRestriction J B U ⋙ derivedSliceMap J B f ≅
      derivedSliceRestriction J B V :=
  (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.mapDerivedCategoryNatIso (sliceRestrictionMapIso J B f)

variable (A D : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))

/-- Restriction of an actual derived morphism, conjugated by the canonical slice isomorphisms.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalHomRestriction {U V : C} (f : V ⟶ U)
    (a : (derivedSliceRestriction J B U).obj A ⟶
      (derivedSliceRestriction J B U).obj D) :
    (derivedSliceRestriction J B V).obj A ⟶
      (derivedSliceRestriction J B V).obj D :=
  (derivedSliceMapIso J B f).inv.app A ≫ (derivedSliceMap J B f).map a ≫
    (derivedSliceMapIso J B f).hom.app D

/-- Restriction of an actual derived isomorphism, with the same canonical identifications.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalIsoRestriction {U V : C} (f : V ⟶ U)
    (a : (derivedSliceRestriction J B U).obj A ≅
      (derivedSliceRestriction J B U).obj D) :
    (derivedSliceRestriction J B V).obj A ≅
      (derivedSliceRestriction J B V).obj D :=
  ((derivedSliceMapIso J B f).app A).symm ≪≫ (derivedSliceMap J B f).mapIso a ≪≫
    (derivedSliceMapIso J B f).app D

private theorem derivedSliceMapIso_symm {U V : C} (f : V ⟶ U) :
    (derivedSliceMapIso J B f).symm = exactComp
      (J.overPullback (ModuleCat.{u + 1} B) U)
      (J.overMapPullback (ModuleCat.{u + 1} B) f)
      (J.overPullback (ModuleCat.{u + 1} B) V)
      (sliceRestrictionMapIso J B f).symm := by
  apply Iso.ext
  simp only [derivedSliceMapIso, exactComp, Iso.symm_hom, Iso.trans_inv,
    Iso.trans_hom,
    Functor.mapDerivedCategoryNatIso_symm]

private noncomputable def sliceMapDerivedId (U : C) :=
  exactId (J.overMapPullback (ModuleCat.{u + 1} B) (𝟙 U))
    (J.overMapPullbackId (ModuleCat.{u + 1} B) U)

private theorem sliceMapDerived_unit (U : C)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))) :
    (derivedSliceMapIso J B (𝟙 U)).inv.app K ≫
      (sliceMapDerivedId J B U).hom.app ((derivedSliceRestriction J B U).obj K) = 𝟙 _ := by
  rw [← Iso.symm_hom, derivedSliceMapIso_symm]
  exact congr_app (exactComp_unit (J.overPullback (ModuleCat.{u + 1} B) U)
    (J.overMapPullback (ModuleCat.{u + 1} B) (𝟙 U))
    (J.overMapPullbackId (ModuleCat.{u + 1} B) U)
    (sliceRestrictionMapIso J B (𝟙 U)).symm (by
      ext F Z x
      dsimp [sliceRestrictionMapIso]
      simp
      rfl)) K

private noncomputable def sliceMapDerivedComp {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :=
  exactComp (J.overMapPullback (ModuleCat.{u + 1} B) f)
    (J.overMapPullback (ModuleCat.{u + 1} B) g)
    (J.overMapPullback (ModuleCat.{u + 1} B) (g ≫ f))
    (J.overMapPullbackComp (ModuleCat.{u + 1} B) g f).symm

private theorem sliceMapDerived_assoc {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))) :
    (derivedSliceMapIso J B g).inv.app K ≫
      (derivedSliceMap J B g).map ((derivedSliceMapIso J B f).inv.app K) =
      (derivedSliceMapIso J B (g ≫ f)).inv.app K ≫
        (sliceMapDerivedComp J B f g).hom.app ((derivedSliceRestriction J B U).obj K) := by
  simp only [← Iso.symm_hom, derivedSliceMapIso_symm]
  exact congr_app (exactComp_assoc
    (J.overPullback (ModuleCat.{u + 1} B) U)
    (J.overMapPullback (ModuleCat.{u + 1} B) f)
    (J.overMapPullback (ModuleCat.{u + 1} B) g)
    (J.overPullback (ModuleCat.{u + 1} B) V)
    (J.overMapPullback (ModuleCat.{u + 1} B) (g ≫ f))
    (J.overPullback (ModuleCat.{u + 1} B) W)
    (sliceRestrictionMapIso J B f).symm
    (J.overMapPullbackComp (ModuleCat.{u + 1} B) g f).symm
    (sliceRestrictionMapIso J B g).symm
    (sliceRestrictionMapIso J B (g ≫ f)).symm (by
      ext F Z x
      dsimp [sliceRestrictionMapIso]
      simp
      rfl)) K

/-- The restriction maps on derived Hom sets satisfy the identity and composition laws.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves)

Proof: On module sheaves the slice restriction identifications are identity maps on sections.
Their identity and cocycle laws therefore hold before deriving. Derive these identities using
the composition comparison for exact functors. Expand the three conjugations in the displayed
formulas, cancel consecutive comparison isomorphisms, and use preservation of identity and
composition by the localized functor. -/
theorem derivedLocalHomRestriction_laws :
    (∀ (U : C) (a : (derivedSliceRestriction J B U).obj A ⟶
      (derivedSliceRestriction J B U).obj D),
      derivedLocalHomRestriction J B A D (𝟙 U) a = a) ∧
    (∀ (U V W : C) (f : V ⟶ U) (g : W ⟶ V)
      (a : (derivedSliceRestriction J B U).obj A ⟶
        (derivedSliceRestriction J B U).obj D),
      derivedLocalHomRestriction J B A D g (derivedLocalHomRestriction J B A D f a) =
        derivedLocalHomRestriction J B A D (g ≫ f) a) := by
  constructor
  · intro U a
    exact conjugate_id (derivedSliceMap J B (𝟙 U)) (sliceMapDerivedId J B U)
      ((derivedSliceMapIso J B (𝟙 U)).app A).symm
      ((derivedSliceMapIso J B (𝟙 U)).app D).symm
      (sliceMapDerived_unit J B U A) (sliceMapDerived_unit J B U D) a
  · intro U V W f g a
    exact (conjugate_comp (derivedSliceMap J B g) (derivedSliceMap J B f)
      (derivedSliceMap J B (g ≫ f)) (sliceMapDerivedComp J B f g)
      ((derivedSliceMapIso J B g).app A).symm
      ((derivedSliceMapIso J B f).app A).symm
      ((derivedSliceMapIso J B (g ≫ f)).app A).symm
      ((derivedSliceMapIso J B g).app D).symm
      ((derivedSliceMapIso J B f).app D).symm
      ((derivedSliceMapIso J B (g ≫ f)).app D).symm
      (sliceMapDerived_assoc J B f g A) (sliceMapDerived_assoc J B f g D) a).symm

/-- The restriction maps on derived isomorphisms satisfy the identity and composition laws.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves)

Proof: Apply the identity and cocycle calculation for derived Hom restriction to the hom
components. Apply it to the inverse components as well. Isomorphisms are determined by their hom
component, giving both equalities. -/
theorem derivedLocalIsoRestriction_laws :
    (∀ (U : C) (a : (derivedSliceRestriction J B U).obj A ≅
      (derivedSliceRestriction J B U).obj D),
      derivedLocalIsoRestriction J B A D (𝟙 U) a = a) ∧
    (∀ (U V W : C) (f : V ⟶ U) (g : W ⟶ V)
      (a : (derivedSliceRestriction J B U).obj A ≅
        (derivedSliceRestriction J B U).obj D),
      derivedLocalIsoRestriction J B A D g (derivedLocalIsoRestriction J B A D f a) =
        derivedLocalIsoRestriction J B A D (g ≫ f) a) := by
  constructor
  · intro U a
    apply Iso.ext
    exact (derivedLocalHomRestriction_laws J B A D).1 U a.hom
  · intro U V W f g a
    apply Iso.ext
    exact (derivedLocalHomRestriction_laws J B A D).2 U V W f g a.hom

/-- The presheaf of actual derived morphisms on localized sites, not underived module Hom.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalHomPresheaf : Cᵒᵖ ⥤ Type (u + 1) where
  obj U := (derivedSliceRestriction J B U.unop).obj A ⟶
    (derivedSliceRestriction J B U.unop).obj D
  map f := ↾(derivedLocalHomRestriction J B A D f.unop)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (derivedLocalHomRestriction_laws J B A D).1 U.unop a
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact ((derivedLocalHomRestriction_laws J B A D).2 _ _ _ f.unop g.unop a).symm

/-- The presheaf of actual derived isomorphisms on localized sites, retaining the inverse data.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalIsoPresheaf : Cᵒᵖ ⥤ Type (u + 1) where
  obj U := (derivedSliceRestriction J B U.unop).obj A ≅
    (derivedSliceRestriction J B U.unop).obj D
  map f := ↾(derivedLocalIsoRestriction J B A D f.unop)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (derivedLocalIsoRestriction_laws J B A D).1 U.unop a
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact ((derivedLocalIsoRestriction_laws J B A D).2 _ _ _ f.unop g.unop a).symm

/-- Sheafification of the presheaf of actual derived morphisms.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev derivedLocalHomSheaf [HasWeakSheafify J (Type (u + 1))] :=
  (presheafToSheaf J (Type (u + 1))).obj (derivedLocalHomPresheaf J B A D)

/-- Sheafification of the presheaf of actual derived isomorphisms.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev derivedLocalIsoSheaf [HasWeakSheafify J (Type (u + 1))] :=
  (presheafToSheaf J (Type (u + 1))).obj (derivedLocalIsoPresheaf J B A D)

omit [EssentiallySmall.{u + 1} C] in
private theorem pairSection_ext [HasWeakSheafify J (Type (u + 1))]
    (F G : Sheaf J (Type (u + 1))) (U : C) (x y : (F ⨯ G).obj.obj (op U))
    (h₁ : (prod.fst : F ⨯ G ⟶ F).hom.app (op U) x =
      (prod.fst : F ⨯ G ⟶ F).hom.app (op U) y)
    (h₂ : (prod.snd : F ⨯ G ⟶ G).hom.app (op U) x =
      (prod.snd : F ⨯ G ⟶ G).hom.app (op U) y) : x = y := by
  let E := sheafToPresheaf J (Type (u + 1)) ⋙
    (evaluation Cᵒᵖ (Type (u + 1))).obj (op U)
  apply (ConcreteCategory.bijective_of_isIso (prodComparison E F G)).injective
  apply (ConcreteCategory.bijective_of_isIso
    (Types.binaryProductIso (E.obj F) (E.obj G)).hom).injective
  apply _root_.Prod.ext
  · have ht : prodComparison E F G ≫
        (Types.binaryProductIso (E.obj F) (E.obj G)).hom ≫
        (↾_root_.Prod.fst : (E.obj F × E.obj G) ⟶ E.obj F) = E.map prod.fst := by
      rw [Types.binaryProductIso_hom_comp_fst, prodComparison_fst]
    change (E.map prod.fst) x = (E.map prod.fst) y at h₁
    simpa only [ConcreteCategory.comp_apply, TypeCat.ofHom_apply] using
      (ConcreteCategory.congr_hom ht x).trans
        (h₁.trans (ConcreteCategory.congr_hom ht y).symm)
  · have ht : prodComparison E F G ≫
        (Types.binaryProductIso (E.obj F) (E.obj G)).hom ≫
        (↾_root_.Prod.snd : (E.obj F × E.obj G) ⟶ E.obj G) = E.map prod.snd := by
      rw [Types.binaryProductIso_hom_comp_snd, prodComparison_snd]
    change (E.map prod.snd) x = (E.map prod.snd) y at h₂
    simpa only [ConcreteCategory.comp_apply, TypeCat.ofHom_apply] using
      (ConcreteCategory.congr_hom ht x).trans
        (h₂.trans (ConcreteCategory.congr_hom ht y).symm)

private noncomputable def presheafPairSection
    (P Q : Cᵒᵖ ⥤ Type (u + 1)) (U : C)
    (s : P.obj (op U)) (t : Q.obj (op U)) : (P ⨯ Q).obj (op U) :=
  inv (prodComparison ((evaluation Cᵒᵖ (Type (u + 1))).obj (op U)) P Q)
    ((Types.binaryProductIso _ _).inv (s, t))

omit [EssentiallySmall.{u + 1} C] in
private theorem presheafPairSection_fst
    (P Q : Cᵒᵖ ⥤ Type (u + 1)) (U : C)
    (s : P.obj (op U)) (t : Q.obj (op U)) :
    (prod.fst : P ⨯ Q ⟶ P).app (op U) (presheafPairSection P Q U s t) = s := by
  unfold presheafPairSection
  change (((evaluation Cᵒᵖ (Type (u + 1))).obj (op U)).map prod.fst) _ = s
  rw [← ConcreteCategory.comp_apply, inv_prodComparison_map_fst,
    ← ConcreteCategory.comp_apply, Types.binaryProductIso_inv_comp_fst]
  rfl

omit [EssentiallySmall.{u + 1} C] in
private theorem presheafPairSection_snd
    (P Q : Cᵒᵖ ⥤ Type (u + 1)) (U : C)
    (s : P.obj (op U)) (t : Q.obj (op U)) :
    (prod.snd : P ⨯ Q ⟶ Q).app (op U) (presheafPairSection P Q U s t) = t := by
  unfold presheafPairSection
  change (((evaluation Cᵒᵖ (Type (u + 1))).obj (op U)).map prod.snd) _ = t
  rw [← ConcreteCategory.comp_apply, inv_prodComparison_map_snd,
    ← ConcreteCategory.comp_apply, Types.binaryProductIso_inv_comp_snd]
  rfl

variable {J B} {A D}

/-- Precomposition and postcomposition commute with restriction of actual derived morphisms.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves)

Proof: Use naturality of the derived slice-restriction comparison on f and g. Expand the
conjugations defining local restriction, use preservation of composition by the local functor,
and cancel the adjacent comparison isomorphisms. The resulting composites on both sides are
identical. -/
theorem derivedLocalHomPresheafMap_natural
    {A' D' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (f : A' ⟶ A) (g : D ⟶ D') (U V : C) (h : V ⟶ U)
    (a : (derivedSliceRestriction J B U).obj A ⟶
      (derivedSliceRestriction J B U).obj D) :
    (derivedSliceRestriction J B V).map f ≫
        derivedLocalHomRestriction J B A D h a ≫
          (derivedSliceRestriction J B V).map g =
      derivedLocalHomRestriction J B A' D' h
        ((derivedSliceRestriction J B U).map f ≫ a ≫
          (derivedSliceRestriction J B U).map g) := by
  dsimp only [derivedLocalHomRestriction]
  simp only [Functor.map_comp, Category.assoc]
  have hf := (derivedSliceMapIso J B h).inv.naturality f
  have hg := (derivedSliceMapIso J B h).hom.naturality g
  dsimp only [Functor.comp_map] at hf hg
  rw [reassoc_of% hf, hg]

/-- The map on local derived Hom presheaves induced by precomposition and postcomposition.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalHomPresheafMap
    {A' D' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (f : A' ⟶ A) (g : D ⟶ D') :
    derivedLocalHomPresheaf J B A D ⟶ derivedLocalHomPresheaf J B A' D' where
  app U := ↾fun a ↦ (derivedSliceRestriction J B U.unop).map f ≫ a ≫
    (derivedSliceRestriction J B U.unop).map g
  naturality := by
    intro U V h
    apply ConcreteCategory.hom_ext
    intro a
    exact derivedLocalHomPresheafMap_natural f g _ _ h.unop a

/-- Sheafification of the natural map on derived Hom presheaves.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev derivedLocalHomSheafMap [HasWeakSheafify J (Type (u + 1))]
    {A' D' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (f : A' ⟶ A) (g : D ⟶ D') :=
  (presheafToSheaf J (Type (u + 1))).map (derivedLocalHomPresheafMap f g)

/-- The natural inclusion of local derived isomorphisms into local derived morphisms.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalIsoToHomPresheaf :
    derivedLocalIsoPresheaf J B A D ⟶ derivedLocalHomPresheaf J B A D where
  app U := ↾fun f ↦ f.hom
  naturality := by intros; rfl

/-- The map from derived Isom to derived Hom after sheafification.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev derivedLocalIsoToHomSheaf [HasWeakSheafify J (Type (u + 1))] :=
  (presheafToSheaf J (Type (u + 1))).map (derivedLocalIsoToHomPresheaf (A := A) (D := D))

variable (J B)

/-- A functor on derived module sheaves with its localized functors and coherent restriction
comparisons. The two naturality fields express precisely that the conjugated local maps give
presheaf maps; no arbitrary map replaces a derived morphism.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
structure DerivedLocalFunctor (B' : Type (u + 1)) [CommRing B'] where
  globalFunctor : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)) ⥤
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} B'))
  localFunctor (U : C) : DerivedCategory (Sheaf (J.over U) (ModuleCat.{u + 1} B)) ⥤
    DerivedCategory (Sheaf (J.over U) (ModuleCat.{u + 1} B'))
  restrictionIso (U : C) : derivedSliceRestriction J B U ⋙ localFunctor U ≅
    globalFunctor ⋙ derivedSliceRestriction J B' U
  hom_naturality (A D : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))
      (U V : C) (h : V ⟶ U)
      (a : (derivedSliceRestriction J B U).obj A ⟶
        (derivedSliceRestriction J B U).obj D) :
    (restrictionIso V).inv.app A ≫
        (localFunctor V).map (derivedLocalHomRestriction J B A D h a) ≫
          (restrictionIso V).hom.app D =
      derivedLocalHomRestriction J B' (globalFunctor.obj A) (globalFunctor.obj D) h
        ((restrictionIso U).inv.app A ≫ (localFunctor U).map a ≫
          (restrictionIso U).hom.app D)
  iso_naturality (A D : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))
      (U V : C) (h : V ⟶ U)
      (a : (derivedSliceRestriction J B U).obj A ≅
        (derivedSliceRestriction J B U).obj D) :
    ((restrictionIso V).app A).symm ≪≫
        (localFunctor V).mapIso (derivedLocalIsoRestriction J B A D h a) ≪≫
          (restrictionIso V).app D =
      derivedLocalIsoRestriction J B' (globalFunctor.obj A) (globalFunctor.obj D) h
        (((restrictionIso U).app A).symm ≪≫ (localFunctor U).mapIso a ≪≫
          (restrictionIso U).app D)

namespace DerivedLocalFunctor
variable {J B} {B' : Type (u + 1)} [CommRing B'] (T : DerivedLocalFunctor J B B')
variable (A D : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))

end DerivedLocalFunctor

variable {B' : Type (u + 1)} [CommRing B']

/-- The canonical commutation of restriction of scalars with localization, given by identity maps.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def sliceRestrictScalarsSheafIso (φ : B →+* B') (U : C) :
    J.overPullback (ModuleCat.{u + 1} B') U ⋙ Sheaf.restrictScalars (J.over U) φ ≅
      Sheaf.restrictScalars J φ ⋙ J.overPullback (ModuleCat.{u + 1} B) U :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The same canonical scalar/restriction commutation on actual derived categories.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def sliceRestrictScalarsIso (φ : B →+* B') (U : C) :
    derivedSliceRestriction J B' U ⋙ Sheaf.derivedRestrictScalars (J.over U) φ ≅
      Sheaf.derivedRestrictScalars J φ ⋙ derivedSliceRestriction J B U :=
  (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.mapDerivedCategoryNatIso
      (sliceRestrictScalarsSheafIso J B φ U) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm

end CategoryTheory
