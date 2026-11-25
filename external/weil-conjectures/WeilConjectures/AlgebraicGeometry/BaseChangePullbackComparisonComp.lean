/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
import WeilConjectures.AlgebraicGeometry.EtalePullbackSingleComp

/-! # Composition of the coefficient comparisons in target transitions

Source: Stacks Tags 0F07 and 09Z1, canonical restriction comparisons.
(blueprint: lem-sbc-pullback-comparison-comp)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

private lemma map_eqToHom_naturality
    {C D : Type*} [Category C] [Category D] (G H : C ⥤ D) (h : G = H)
    {X Y : C} (f : X ⟶ Y) :
    G.map f ≫ eqToHom (congrArg (fun J : C ⥤ D ↦ J.obj Y) h) =
      eqToHom (congrArg (fun J : C ⥤ D ↦ J.obj X) h) ≫ H.map f := by
  subst h
  simp

private lemma comp_hom_app_eq
    {T S R : Scheme.{u}} (f : T ⟶ S) (g : S ⟶ R) (fg : T ⟶ R)
    (hh : fg = f ≫ g)
    (K : DerivedCategory.Plus (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) f g fg hh).hom.app K =
      eqToHom (by rw [hh]) ≫
        (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) f g).hom.app K := by
  subst hh
  exact (Category.id_comp _).symm

private lemma comp_inv_app_eq
    {T S R : Scheme.{u}} (f : T ⟶ S) (g : S ⟶ R) (fg : T ⟶ R)
    (hh : fg = f ≫ g)
    (K : DerivedCategory.Plus (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) f g fg hh).inv.app K =
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) f g).inv.app K ≫
        eqToHom (by rw [hh]) := by
  subst hh
  exact (Category.comp_id _).symm

private lemma map_comp_hom_comp_inv
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+((f)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) g h gh hgh).hom.app K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) f g fg hfg).inv.app
        (D+((h)^*[ModuleCat.{u + 1} Λ]).obj K) =
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) f gh fgh
        (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) fg h fgh hfgh).hom.app K := by
  have key := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc
    (ModuleCat.{u + 1} Λ) f g h fg gh fgh hfg hgh hfgh) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at key
  simpa using comp_inv_eq_inv_comp_of_eq _ _ _ _ key

private lemma comp_hom_map_comp_inv
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) f g fg hfg).hom.app
        (D+((h)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      D+((f)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) g h gh hgh).inv.app K) =
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) fg h fgh hfgh).inv.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) f gh fgh
        (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K := by
  have key := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc
    (ModuleCat.{u + 1} Λ) f g h fg gh fgh hfg hgh hfgh) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at key
  have hh := comp_inv_eq_inv_comp_of_eq _ _ _ _ key.symm
  rwa [NatIso.inv_hom_app, ← Functor.map_inv, NatIso.inv_hom_app] at hh

private lemma map_comp_inv_comp_inv
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+((f)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) g h).inv.app K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) f (g ≫ h) ((f ≫ g) ≫ h)
        (Category.assoc f g h).symm).inv.app K =
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) f g).inv.app
        (D+((h)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (f ≫ g) h).inv.app K := by
  have key := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc
    (ModuleCat.{u + 1} Λ) f g h (f ≫ g) (g ≫ h) ((f ≫ g) ≫ h) rfl rfl rfl) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at key
  have hk :
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) f (g ≫ h) ((f ≫ g) ≫ h)
        (Category.assoc f g h).symm).app K ≪≫
        D+((f)^*[ModuleCat.{u + 1} Λ]).mapIso
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) g h).app K) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (f ≫ g) h).app K ≪≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) f g).app
          (D+((h)^*[ModuleCat.{u + 1} Λ]).obj K) := Iso.ext key
  have hh := congrArg Iso.inv hk
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at hh
  exact hh

private lemma square_comp
    {T Y T₁ T₂ Y₁ Y₂ : Scheme.{u}} (e : Y ⟶ T)
    (π₂ : T₂ ⟶ T) (a₂ : Y₂ ⟶ Y) (e₂ : Y₂ ⟶ T₂)
    (wa₂ : a₂ ≫ e = e₂ ≫ π₂)
    (π₁ : T₁ ⟶ T₂) (a₁ : Y₁ ⟶ Y₂) (e₁ : Y₁ ⟶ T₁)
    (wa₁ : a₁ ≫ e₂ = e₁ ≫ π₁)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₂ e).inv.app K ≫
          eqToHom (by rw [wa₂]) ≫
          (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e₂ π₂).hom.app K) ≫
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ e₂).inv.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      eqToHom (by rw [wa₁]) ≫
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e₁ π₁).hom.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) π₁ π₂).inv.app K) =
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ a₂).inv.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) (a₁ ≫ a₂) e).inv.app K ≫
      eqToHom (by rw [Category.assoc, wa₂, ← Category.assoc, wa₁, Category.assoc]) ≫
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e₁ (π₁ ≫ π₂)).hom.app K := by
  have hc :
      D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e).inv.app K ≫
            (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₂ π₂
              (a₂ ≫ e) wa₂).hom.app K) ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ e₂).inv.app
          (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π₁
          (a₁ ≫ e₂) wa₁).hom.app (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) π₁ π₂).inv.app K) =
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ a₂).inv.app
          (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) (a₁ ≫ a₂) e).inv.app K ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ (π₁ ≫ π₂)
          ((a₁ ≫ a₂) ≫ e)
          (by
            calc
              (a₁ ≫ a₂) ≫ e = (a₁ ≫ e₂) ≫ π₂ := by
                rw [Category.assoc, wa₂, Category.assoc]
              _ = e₁ ≫ (π₁ ≫ π₂) := by rw [wa₁, Category.assoc])).hom.app K := by
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% map_comp_hom_comp_inv Λ a₁ e₂ π₂ (a₁ ≫ e₂) (a₂ ≫ e)
      ((a₁ ≫ a₂) ≫ e) rfl wa₂
      (by rw [Category.assoc, wa₂, Category.assoc]) K]
    rw [comp_hom_map_comp_inv Λ e₁ π₁ π₂ (a₁ ≫ e₂) (π₁ ≫ π₂)
      ((a₁ ≫ a₂) ≫ e) wa₁ rfl
      (by rw [Category.assoc, wa₂, Category.assoc]) K]
    rw [Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% map_comp_inv_comp_inv Λ a₁ a₂ e K]
    rfl
  simp only [comp_hom_app_eq, comp_inv_app_eq, eqToHom_refl,
    Category.comp_id, Functor.map_comp, Category.assoc] at hc
  simpa only [Functor.map_comp, Category.assoc] using hc

/-- The pullback and single-complex comparisons for two commutative squares compose.

Source: Stacks Tag 0F07, condition (1), and Tag 09Z1, the canonical restriction maps.
(blueprint: lem-sbc-pullback-comparison-comp)

Proof: write each square comparison as the inverse composition comparison for its
upper-left path followed by the comparison for its lower-right path. Apply associativity
of the derived pullback comparisons to the triples (a₁,a₂,e), (a₁,e₂,π₂), and
(e₁,π₁,π₂). Naturality moves the identification π₂^*(F[0]) → (π₂^*F)[0]
past the (a₁,e₂) comparison. The intermediate comparison and its inverse cancel.
For the remaining coefficient maps, composition of the exact functors π₂^* and π₁^*
commutes with placing a sheaf in degree zero: on a single complex both maps are the
underived composition comparison in degree zero and the unique zero maps elsewhere.
The localization factorization and the fully faithful inclusion D⁺ → D preserve this
identity. After applying e₁^*, this identifies the two single-complex maps followed by
(π₁^*π₂^*F)[0] → ((π₁ ≫ π₂)^*F)[0] with the single-complex comparison for π₁ ≫ π₂.
The uncancelled source comparison is precisely the inverse comparison for a₁,a₂.
This uses only commutativity of the two squares, not cartesianness; identity arrows and
zero sheaves give the same identities by the unit laws.
-/
theorem Etale.baseChangePullbackComparison_comp
    {T Y T₁ T₂ Y₁ Y₂ : Scheme.{u}} (e : Y ⟶ T)
    (π₂ : T₂ ⟶ T) (a₂ : Y₂ ⟶ Y) (e₂ : Y₂ ⟶ T₂)
    (wa₂ : a₂ ≫ e = e₂ ≫ π₂)
    (π₁ : T₁ ⟶ T₂) (a₁ : Y₁ ⟶ Y₂) (e₁ : Y₁ ⟶ T₁)
    (wa₁ : a₁ ≫ e₂ = e₁ ≫ π₁)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
    let c₂ := (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₂ e).inv.app K ≫
      eqToHom (by rw [wa₂]) ≫
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e₂ π₂).hom.app K ≫
      D+((e₂)^*[ModuleCat.{u + 1} Λ]).map
        ((((π₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
    let c₁ := (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ e₂).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
      eqToHom (by rw [wa₁]) ≫
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e₁ π₁).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
      D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
        ((((π₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F))
    let c₀ := (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) (a₁ ≫ a₂) e).inv.app K ≫
      eqToHom (by rw [Category.assoc, wa₂, ← Category.assoc, wa₁, Category.assoc]) ≫
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e₁ (π₁ ≫ π₂)).hom.app K ≫
      D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
        ((((π₁ ≫ π₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
    D+((a₁)^*[ModuleCat.{u + 1} Λ]).map c₂ ≫ c₁ ≫
        D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) π₁ π₂ (π₁ ≫ π₂) rfl).inv.app F)) =
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ a₂).inv.app
          (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫ c₀ := by
  dsimp only
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let t := (((π₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F
  have hn := (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ e₂).inv.naturality t
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  have ht := map_eqToHom_naturality
    D+((a₁ ≫ e₂)^*[ModuleCat.{u + 1} Λ]) D+((e₁ ≫ π₁)^*[ModuleCat.{u + 1} Λ])
    (by rw [wa₁]) t
  rw [reassoc_of% ht]
  have hn' := (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e₁ π₁).hom.naturality t
  simp only [Functor.comp_map] at hn'
  rw [reassoc_of% hn']
  slice_lhs 7 9 =>
    rw [← Functor.map_comp, ← Functor.map_comp]
    rw [Etale.upperStarPlusComp_single Λ π₁ π₂ F, Functor.map_comp]
  have hs := square_comp Λ e π₂ a₂ e₂ wa₂ π₁ a₁ e₁ wa₁ K
  simp only [Functor.map_comp, Category.assoc] at hs
  rw [reassoc_of% hs]

end AlgebraicGeometry
