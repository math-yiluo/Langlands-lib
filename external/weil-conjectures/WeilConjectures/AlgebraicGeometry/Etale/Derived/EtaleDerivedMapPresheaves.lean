/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-!
# Presheaves of derived etale maps

Source: Stacks Project, sites-cohomology.tex, Tag 09BE, lemma-locally-constant-map,
and the derived Hom presheaf used in the finite-ring extension of that lemma
(blueprint: def-weil-pbc-etale-derived-map-presheaves).
-/

@[expose] public section

universe u u'

open CategoryTheory Opposite

open CategoryTheory.Limits

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

namespace AlgebraicGeometry.Etale

variable {X : Scheme.{u}} (B : Type (u + 1)) [CommRing B]

/-- The comparison between restriction to `U` and restriction first to `V` then to `U`.
Source: Stacks, Tag 09BE, restriction of derived maps
(blueprint: def-weil-pbc-etale-derived-map-presheaves). -/
noncomputable def derivedMapRestrictionIso {U V : X.Etale} (f : U ⟶ V)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K ≅
      (upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory.obj
        ((upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj K) :=
  (Functor.mapDerivedCategoryNatIso
    (upperStarComp (ModuleCat.{u + 1} B) f.left V.hom U.hom f.w.symm) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).app K

/-- Restrict a derived morphism along an arrow of the small etale site.
Source: Stacks, Tag 09BE (blueprint: def-weil-pbc-etale-derived-map-presheaves). -/
noncomputable def restrictDerivedMap
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    {U V : X.Etale} (f : U ⟶ V)
    (a : (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj K ⟶
      (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj L) :
    (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K ⟶
      (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj L :=
  (derivedMapRestrictionIso B f K).hom ≫
    (upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory.map a ≫
      (derivedMapRestrictionIso B f L).inv

/-- Restrict an isomorphism in the same manner.
Source: Stacks, Tag 09BE (blueprint: def-weil-pbc-etale-derived-map-presheaves). -/
noncomputable def restrictDerivedIso
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    {U V : X.Etale} (f : U ⟶ V)
    (a : (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj K ≅
      (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj L) :
    (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K ≅
      (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj L :=
  derivedMapRestrictionIso B f K ≪≫
    (upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory.mapIso a ≪≫
      (derivedMapRestrictionIso B f L).symm

attribute [local irreducible] upperStar upperStarComp upperStarId

section PullbackCoherence

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

private noncomputable def mapPullbackComp {T S R : Scheme.{u}}
    (f : T ⟶ S) (g : S ⟶ R) (fg : T ⟶ R) (hfg : fg = f ≫ g) :
    (upperStar A fg).mapDerivedCategory ≅
      (upperStar A g).mapDerivedCategory ⋙
        (upperStar A f).mapDerivedCategory :=
  exactComp (upperStar A g)
    (upperStar A f) (upperStar A fg)
    (upperStarComp A f g fg hfg)

private lemma mapPullbackComp_assoc {W Y Z R : Scheme.{u}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ R)
    (fg : W ⟶ Z) (gh : Y ⟶ R) (fgh : W ⟶ R)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) :
    (mapPullbackComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
        Functor.whiskerRight (mapPullbackComp A g h gh hgh).hom
          (upperStar A f).mapDerivedCategory =
      (mapPullbackComp A fg h fgh hfgh).hom ≫
        Functor.whiskerLeft (upperStar A h).mapDerivedCategory
          (mapPullbackComp A f g fg hfg).hom := by
  exact exactComp_assoc _ _ _ _ _ _ _ _ _ _
    (upperStarComp_assoc' A f g h fg gh fgh hfg hgh hfgh)

private noncomputable def mapPullbackId (T : Scheme.{u}) :
    (upperStar A (𝟙 T)).mapDerivedCategory ≅
      𝟭 (DerivedCategory (Sheaf T.smallEtaleTopology A)) :=
  exactId (upperStar A (𝟙 T))
    (upperStarId A T)

private lemma mapPullbackComp_id_left {T S : Scheme.{u}} (g : T ⟶ S)
    (K : DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    (mapPullbackComp A (𝟙 T) g g (Category.id_comp g).symm).hom.app K ≫
      (mapPullbackId A T).hom.app
        ((upperStar A g).mapDerivedCategory.obj K) = 𝟙 _ := by
  apply NatTrans.congr_app
    (exactComp_unit (upperStar A g)
      (upperStar A (𝟙 T))
      (upperStarId A T)
      (upperStarComp A (𝟙 T) g g (Category.id_comp g).symm) ?_) K
  ext Q
  simp [upperStarComp_id_left]

end PullbackCoherence

private lemma restriction_unit (U : X.Etale)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (derivedMapRestrictionIso B (𝟙 U) K).hom ≫
      (mapPullbackId (ModuleCat.{u + 1} B) U.left).hom.app
        ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K) = 𝟙 _ := by
  exact mapPullbackComp_id_left (ModuleCat.{u + 1} B) U.hom K

private lemma restriction_assoc {U V W : X.Etale} (f : U ⟶ V) (g : V ⟶ W)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (derivedMapRestrictionIso B f K).hom ≫
      (upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory.map
        (derivedMapRestrictionIso B g K).hom =
      (derivedMapRestrictionIso B (f ≫ g) K).hom ≫
        (mapPullbackComp (ModuleCat.{u + 1} B) f.left g.left (f ≫ g).left rfl).hom.app
          ((upperStar (ModuleCat.{u + 1} B) W.hom).mapDerivedCategory.obj K) := by
  exact NatTrans.congr_app
    (mapPullbackComp_assoc (ModuleCat.{u + 1} B) f.left g.left W.hom (f ≫ g).left V.hom U.hom
      rfl g.w.symm (f ≫ g).w.symm) K

private lemma restrictDerivedMap_id
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (U : X.Etale)
    (a : (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K ⟶
      (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj L) :
    restrictDerivedMap B (𝟙 U) a = a := by
  exact conjugate_id
    (upperStar (ModuleCat.{u + 1} B) (𝟙 U.left)).mapDerivedCategory
    (mapPullbackId (ModuleCat.{u + 1} B) U.left)
    (derivedMapRestrictionIso B (𝟙 U) K) (derivedMapRestrictionIso B (𝟙 U) L)
    (restriction_unit B U K) (restriction_unit B U L) a

private lemma restrictDerivedMap_comp
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (U V W : X.Etale) (f : U ⟶ V) (g : V ⟶ W)
    (a : (upperStar (ModuleCat.{u + 1} B) W.hom).mapDerivedCategory.obj K ⟶
      (upperStar (ModuleCat.{u + 1} B) W.hom).mapDerivedCategory.obj L) :
    restrictDerivedMap B (f ≫ g) a =
      restrictDerivedMap B f (restrictDerivedMap B g a) := by
  exact conjugate_comp
    (upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} B) g.left).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} B) (f ≫ g).left).mapDerivedCategory
    (mapPullbackComp (ModuleCat.{u + 1} B) f.left g.left (f ≫ g).left rfl)
    (derivedMapRestrictionIso B f K) (derivedMapRestrictionIso B g K)
    (derivedMapRestrictionIso B (f ≫ g) K)
    (derivedMapRestrictionIso B f L) (derivedMapRestrictionIso B g L)
    (derivedMapRestrictionIso B (f ≫ g) L)
    (restriction_assoc B f g K) (restriction_assoc B f g L) a

/-- The restriction functions satisfy the presheaf laws.
Source: Stacks, Tag 09BE (blueprint: def-weil-pbc-etale-derived-map-presheaves).
Proof: restriction to an identity is the identity by the unit coherence of pullback.
The pullback associativity coherence identifies restriction along a composite with
successive restriction. Apply the corresponding composition comparisons on derived
categories; the middle comparison and its inverse cancel. For isomorphisms the same
calculation applies to the forward and inverse arrows. -/
theorem derivedMapRestriction_laws
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (∀ (U : X.Etale) (a), restrictDerivedMap B (K := K) (L := L) (𝟙 U) a = a) ∧
    (∀ (U V W : X.Etale) (f : U ⟶ V) (g : V ⟶ W) (a),
      restrictDerivedMap B (K := K) (L := L) (f ≫ g) a =
        restrictDerivedMap B f (restrictDerivedMap B g a)) ∧
    (∀ (U : X.Etale) (a), restrictDerivedIso B (K := K) (L := L) (𝟙 U) a = a) ∧
    (∀ (U V W : X.Etale) (f : U ⟶ V) (g : V ⟶ W) (a),
      restrictDerivedIso B (K := K) (L := L) (f ≫ g) a =
        restrictDerivedIso B f (restrictDerivedIso B g a)) := by
  refine ⟨restrictDerivedMap_id B K L, ?_, ?_, ?_⟩
  · exact restrictDerivedMap_comp B K L
  · intro U a
    apply Iso.ext
    exact restrictDerivedMap_id B K L U a.hom
  · intro U V W f g a
    apply Iso.ext
    exact restrictDerivedMap_comp B K L U V W f g a.hom

/-- The presheaf `U ↦ Hom(K|U,L|U)` in the derived categories of etale module sheaves.
Source: Stacks, Tag 09BE (blueprint: def-weil-pbc-etale-derived-map-presheaves). -/
noncomputable def derivedHomPresheaf
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    X.Etaleᵒᵖ ⥤ Type (u + 1) where
  obj U := (upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.obj K ⟶
    (upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.obj L
  map f := TypeCat.ofHom (restrictDerivedMap B (K := K) (L := L) f.unop)
  map_id U := ConcreteCategory.hom_ext _ _ ((derivedMapRestriction_laws B K L).1 U.unop)
  map_comp f g :=
    ConcreteCategory.hom_ext _ _ ((derivedMapRestriction_laws B K L).2.1 _ _ _ g.unop f.unop)

/-- The presheaf `U ↦ Isom(K|U,L|U)`, which can take the empty value.
Source: Stacks, Tag 09BE (blueprint: def-weil-pbc-etale-derived-map-presheaves). -/
noncomputable def derivedIsoPresheaf
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    X.Etaleᵒᵖ ⥤ Type (u + 1) where
  obj U := (upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.obj K ≅
    (upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.obj L
  map f := TypeCat.ofHom (restrictDerivedIso B (K := K) (L := L) f.unop)
  map_id U := ConcreteCategory.hom_ext _ _ ((derivedMapRestriction_laws B K L).2.2.1 U.unop)
  map_comp f g :=
    ConcreteCategory.hom_ext _ _ ((derivedMapRestriction_laws B K L).2.2.2 _ _ _ g.unop f.unop)

end AlgebraicGeometry.Etale
