/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SpecializationCospecializationArrows
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
import WeilConjectures.AlgebraicGeometry.DerivedGlobalGermExchange

/-! # Fibre maps and restriction after an arbitrary base change

Source: Stacks Project, Tags 01F8, 08J6 and 0GJV.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem inv_comparison_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (K : HomotopyCategory.Plus C) :
    ((mapDerivedCategoryPlusCompIso F G).symm ≪≫ mapDerivedCategoryPlusNatIso e).inv.app
        (DerivedCategory.Plus.Qh.obj K) ≫
      G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K) =
    H.mapDerivedCategoryPlusFactorsh.hom.app K ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.inv).app K) := by
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryPlusCompIso_hom_app_factorsh]
  apply (cancel_epi ((mapDerivedCategoryPlusNatIso e).hom.app _)).mp
  rw [Iso.hom_inv_id_app_assoc, mapDerivedCategoryPlusNatIso_hom_app_factorsh_assoc]
  rw [← DerivedCategory.Plus.Qh.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategoryPlus_comp]
  simp only [Iso.hom_inv_id]
  rw [NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
    DerivedCategory.Plus.Qh.map_id, Category.comp_id]

private theorem comparison_pasting
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory B]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B)
    (L : C ⥤ E) (S : D ⥤ B) (T : C ⥤ B)
    [F.Additive] [G.Additive] [H.Additive] [L.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (a : F ⋙ S ≅ T) (b : G ⋙ H ≅ S) (c : L ⋙ H ≅ T) (d : L ≅ F ⋙ G)
    (hq : ∀ X : C, a.inv.app X ≫ b.inv.app (F.obj X) =
      c.inv.app X ≫ H.map (d.hom.app X)) (K : DerivedCategory.Plus C) :
    ((mapDerivedCategoryPlusCompIso F S).symm ≪≫ mapDerivedCategoryPlusNatIso a).inv.app K ≫
      ((mapDerivedCategoryPlusCompIso G H).symm ≪≫ mapDerivedCategoryPlusNatIso b).inv.app
        (F.mapDerivedCategoryPlus.obj K) =
    ((mapDerivedCategoryPlusCompIso L H).symm ≪≫ mapDerivedCategoryPlusNatIso c).inv.app K ≫
      H.mapDerivedCategoryPlus.map
        ((mapDerivedCategoryPlusNatIso d ≪≫ mapDerivedCategoryPlusCompIso F G).hom.app K) := by
  have hqh (X : HomotopyCategory.Plus C) :
      (NatTrans.mapHomotopyCategoryPlus a.inv).app X ≫
        (NatTrans.mapHomotopyCategoryPlus b.inv).app (F.mapHomotopyCategoryPlus.obj X) =
      (NatTrans.mapHomotopyCategoryPlus c.inv).app X ≫
        H.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus d.hom).app X) := by
    apply (HomotopyCategory.Plus.ι B).map_injective
    obtain ⟨⟨X⟩, hX⟩ := X
    change (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map _ ≫
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map _ =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map _ ≫
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map _
    simp only [← Functor.map_comp]
    congr 1
    ext n
    exact hq (X.X n)
  let A := (mapDerivedCategoryPlusCompIso F S).symm ≪≫ mapDerivedCategoryPlusNatIso a
  let B' := (mapDerivedCategoryPlusCompIso G H).symm ≪≫ mapDerivedCategoryPlusNatIso b
  let C' := (mapDerivedCategoryPlusCompIso L H).symm ≪≫ mapDerivedCategoryPlusNatIso c
  let D' := mapDerivedCategoryPlusNatIso d ≪≫ mapDerivedCategoryPlusCompIso F G
  let τ₁ := A.inv ≫ whiskerLeft F.mapDerivedCategoryPlus B'.inv
  let τ₂ := C'.inv ≫ whiskerRight D'.hom H.mapDerivedCategoryPlus
  have ht : τ₁ = τ₂ := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)
    intro X
    dsimp only [τ₁, τ₂, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
    apply (cancel_mono
      (H.mapDerivedCategoryPlus.map
        (G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app X)) ≫
       H.mapDerivedCategoryPlus.map
        (G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj X)) ≫
       H.mapDerivedCategoryPlusFactorsh.hom.app
        (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj X)))).mp
    have hd : D'.hom.app (DerivedCategory.Plus.Qh.obj X) ≫
        G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app X) ≫
        G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj X) =
      L.mapDerivedCategoryPlusFactorsh.hom.app X ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus d.hom).app X) := by
      dsimp only [D', Iso.trans_hom, NatTrans.comp_app]
      rw [Category.assoc, mapDerivedCategoryPlusCompIso_hom_app_factorsh,
        mapDerivedCategoryPlusNatIso_hom_app_factorsh]
    have hr : C'.inv.app (DerivedCategory.Plus.Qh.obj X) ≫
        H.mapDerivedCategoryPlus.map (D'.hom.app (DerivedCategory.Plus.Qh.obj X)) ≫
        H.mapDerivedCategoryPlus.map
          (G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app X)) ≫
        H.mapDerivedCategoryPlus.map
          (G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj X)) ≫
        H.mapDerivedCategoryPlusFactorsh.hom.app
          (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj X)) =
      T.mapDerivedCategoryPlusFactorsh.hom.app X ≫ DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus c.inv).app X ≫
          H.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus d.hom).app X)) := by
      rw [← H.mapDerivedCategoryPlus.map_comp_assoc,
        ← H.mapDerivedCategoryPlus.map_comp_assoc, Category.assoc, hd,
        H.mapDerivedCategoryPlus.map_comp_assoc]
      erw [H.mapDerivedCategoryPlusFactorsh.hom.naturality]
      simp only [Functor.comp_map]
      erw [reassoc_of% (inv_comparison_fac L H T c X)]
      simp only [Functor.map_comp]
    simp only [Category.assoc]
    rw [hr]
    have hn := B'.inv.naturality (F.mapDerivedCategoryPlusFactorsh.hom.app X)
    dsimp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    erw [inv_comparison_fac G H S b (F.mapHomotopyCategoryPlus.obj X)]
    erw [reassoc_of% (inv_comparison_fac F S T a X)]
    simpa only [Functor.map_comp, Category.assoc] using congrArg
      (fun z ↦ T.mapDerivedCategoryPlusFactorsh.hom.app X ≫ DerivedCategory.Plus.Qh.map z)
      (hqh X)
  exact NatTrans.congr_app ht K

end CategoryTheory.Functor

namespace CategoryTheory.Functor

private theorem mapNat_transport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G) (h : G = H) :
    mapDerivedCategoryPlusNatIso (e ≪≫ eqToIso h) =
      mapDerivedCategoryPlusNatIso e ≪≫ eqToIso (by subst H; rfl) := by
  subst H
  simp only [eqToIso_refl, Iso.trans_refl]

end CategoryTheory.Functor

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The derived global-section germ, before any direct-image Leray comparison.
Source: Stacks Project, Tag 03Q1. -/
noncomputable def derivedGlobalGermAt {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S) :
    (Sheaf.Γ S.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ⟶
      (Scheme.pointSmallEtale t).sheafFiber.mapDerivedCategoryPlus :=
  Functor.rightDerivedFunctorPlusNatTrans (globalGerm t) ≫
    (Scheme.pointSmallEtale t).sheafFiber.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom

/-- The exact inverse-image stalk comparison, descended to bounded-below complexes.
Source: Stacks Project, Tag 03Q1 (3). -/
noncomputable def derivedPullbackStalkIso {S T : Scheme.{u}} (g : T ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    (upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlus ⋙
        (Scheme.pointSmallEtale t).sheafFiber.mapDerivedCategoryPlus ≅
      (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} g t)

private theorem derive_germ_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (H F G : C ⥤ D) [H.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : H ⟶ G) (e : F ≅ G) :
    Functor.rightDerivedFunctorPlusNatTrans a ≫
        G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom ≫
        (Functor.mapDerivedCategoryPlusNatIso e).inv =
      Functor.rightDerivedFunctorPlusNatTrans (a ≫ e.inv) ≫
        F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom := by
  apply Functor.rightDerived_ext H.rightDerivedFunctorPlus H.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso _) _ _ _
  ext M : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Functor.rightDerivedFunctorPlusNatTrans_app_assoc,
    Functor.rightDerivedFunctorPlusNatTrans_app_assoc]
  have hG := NatTrans.congr_app G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac M
  have hF := NatTrans.congr_app F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hG hF
  rw [reassoc_of% hG, hF]
  rw [← cancel_mono ((Functor.mapDerivedCategoryPlusNatIso e).hom.app _)]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← cancel_mono (G.mapDerivedCategoryPlusFactorsh.hom.app M)]
  have he := Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh e M
  simp only [Category.assoc]
  rw [he]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rw [← DerivedCategory.Plus.Qh.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategoryPlus_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact Category.comp_id _

-- The unit formula is checked before passing to the localization of complexes.
private theorem pullback_unit_germ
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    (G : Sheaf X.smallEtaleTopology (AddCommGrpCat.{u + 1})) (U : X.Etale)
    (v : (Scheme.pointSmallEtale (t ≫ f)).fiber.obj U) :
    ((upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) f).unit.app G).hom.app
        (Opposite.op U) ≫
      (Scheme.pointSmallEtale t).toPresheafFiber (f.Etale.obj U)
        ((Scheme.pointSmallEtaleFiberEtaleIso f t).inv.app U v)
        ((f)^*[AddCommGrpCat.{u + 1}].obj G).obj ≫
      ((upperStarCompSheafFiberIso (AddCommGrpCat.{u + 1}) f t).app G).hom =
    (Scheme.pointSmallEtale (t ≫ f)).toPresheafFiber U v G.obj := by
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv _).1
  simp only [upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc,
    GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  erw [show (Scheme.pointSmallEtale t).sheafFiber.map _ =
    (Scheme.pointSmallEtale t).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) (AddCommGrpCat.{u + 1})
      (X.smallGrothendieckTopology (P := @Etale))
      (Y.smallGrothendieckTopology (P := @Etale)))
    (upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) f) G
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (Opposite.op U)
  erw [← Category.assoc, ← huU]
  rfl

private theorem stalk_pasting_underived {S T : Scheme.{u}} (g : T ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} g t).inv.app G ≫
      (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} t
        (𝟙 (Spec (.of Ω)))).inv.app ((upperStar AddCommGrpCat.{u + 1} g).obj G) =
    eqToHom (congrArg (fun y : Spec (.of Ω) ⟶ S ↦
      (Scheme.pointSmallEtale y).sheafFiber.obj G)
      (Category.id_comp (t ≫ g)).symm) ≫
      (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} (t ≫ g)
        (𝟙 (Spec (.of Ω)))).inv.app G ≫
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
        ((upperStarComp AddCommGrpCat.{u + 1} t g).hom.app G) := by
  let G' := (upperStar AddCommGrpCat.{u + 1} g).obj G
  let G'' := (upperStar AddCommGrpCat.{u + 1} t).obj G'
  let C := (upperStarComp AddCommGrpCat.{u + 1} t g).hom.app G
  let z := 𝟙 (Spec (.of Ω))
  apply (Scheme.pointSmallEtale (t ≫ g)).presheafFiber_hom_ext
  intro U v
  let vg := (Scheme.pointSmallEtaleFiberEtaleIso g t).inv.app U v
  let vt := (Scheme.pointSmallEtaleFiberEtaleIso t z).inv.app (g.Etale.obj U) vg
  let vo := (Scheme.pointSmallEtaleFiberEtaleIso (t ≫ g) z).inv.app U v
  have germ_inv {X Y : Scheme.{u}} (f : Y ⟶ X)
      (s : Spec (.of Ω) ⟶ Y)
      (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : X.Etale)
      (w : (Scheme.pointSmallEtale (s ≫ f)).fiber.obj W) :
      (Scheme.pointSmallEtale (s ≫ f)).toPresheafFiber W w Q.obj ≫
        (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f s).inv.app Q =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app Q).hom.app (Opposite.op W) ≫
        (Scheme.pointSmallEtale s).toPresheafFiber (f.Etale.obj W)
          ((Scheme.pointSmallEtaleFiberEtaleIso f s).inv.app W w)
          ((upperStar AddCommGrpCat.{u + 1} f).obj Q).obj := by
    rw [← pullback_unit_germ f s Q W w]
    simp only [Category.assoc, Iso.app_hom, Iso.hom_inv_id_app]
    exact congrArg (_ ≫ ·) (Category.comp_id _)
  erw [← Category.assoc, germ_inv g t G U v]
  erw [Category.assoc, germ_inv t z G' (g.Etale.obj U) vg]
  -- Equality transport for the identity point is definitionally trivial.
  dsimp only [z] at *
  have ho := germ_inv (t ≫ g) z G U v
  dsimp only [z] at ho
  erw [reassoc_of% ho]
  erw [show (Scheme.pointSmallEtale z).sheafFiber.map C =
      (Scheme.pointSmallEtale z).presheafFiber.map C.hom from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := congrArg (fun φ ↦ φ.hom.app (Opposite.op U))
    (upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} t g G)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.comp_unit_app] at hu
  have hpt : (Scheme.pointSmallEtale z).fiber.map
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) t g).hom.app U)
      vo = vt := by
    apply CategoryTheory.Over.OverMorphism.ext
    change vo.left ≫ _ = vt.left
    have h₁ := MorphismProperty.Over.w
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) t g).hom.app U)
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · calc _ = vo.left ≫ pullback.fst U.hom (t ≫ g) := by
                simp only [Category.assoc]
                exact congrArg (_ ≫ ·)
                  (MorphismProperty.Over.pullbackComp_left_fst_fst t g U)
          _ = v.left := Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_fst _ _ _ _
          _ = _ := by
            rw [← Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_fst g t U v,
              Category.assoc]
            exact congrArg (· ≫ pullback.fst U.hom g)
              (Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_fst t z _ vg).symm
      · calc _ = vo.left ≫ pullback.snd U.hom (t ≫ g) ≫ t := by
                simp only [Category.assoc]
                refine congrArg (_ ≫ ·) ?_
                refine (congrArg (_ ≫ ·) pullback.condition).trans ?_
                rw [← Category.assoc]
                exact congrArg (· ≫ t) h₁
          _ = z ≫ t := by
                rw [← Category.assoc]
                exact congrArg (· ≫ t)
                  (Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_snd _ _ _ _)
          _ = _ := by
            exact ((congrArg (fun a ↦ a ≫ pullback.snd U.hom g)
              (Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_fst t z _ vg)).trans
                (CategoryTheory.Over.w vg)).symm
    · calc _ = vo.left ≫ pullback.snd U.hom (t ≫ g) := by
                simp only [Category.assoc]
                exact congrArg (_ ≫ ·) h₁
          _ = z := Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_snd _ _ _ _
          _ = _ := (Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_snd t z _ vg).symm
  let α := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app G).hom.app
      (Opposite.op U) ≫
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G').hom.app
      (Opposite.op (g.Etale.obj U))
  let β := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (t ≫ g)).unit.app G).hom.app
    (Opposite.op U)
  let j := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) t g).hom.app U
  let k := (Scheme.pointSmallEtale z).toPresheafFiber ((t ≫ g).Etale.obj U) vo G''.obj
  have hu' : β ≫ C.hom.app (Opposite.op ((t ≫ g).Etale.obj U)) =
      α ≫ G''.obj.map j.op := hu
  have hk : G''.obj.map j.op ≫ k =
      (Scheme.pointSmallEtale z).toPresheafFiber (t.Etale.obj (g.Etale.obj U)) vt G''.obj := by
    dsimp only [k, j]
    erw [GrothendieckTopology.Point.toPresheafFiber_w, hpt]
    rfl
  calc
    _ = α ≫ (G''.obj.map j.op ≫ k) := congrArg (α ≫ ·) hk.symm
    _ = (α ≫ G''.obj.map j.op) ≫ k := (Category.assoc _ _ _).symm
    _ = (β ≫ C.hom.app (Opposite.op ((t ≫ g).Etale.obj U))) ≫ k :=
      congrArg (· ≫ k) hu'.symm
    _ = _ := Category.assoc _ _ _

private noncomputable def normalizedStalkIso {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S) :
    upperStar AddCommGrpCat.{u + 1} t ⋙
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber ≅
    (Scheme.pointSmallEtale t).sheafFiber :=
  upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} t (𝟙 (Spec (.of Ω))) ≪≫
    eqToIso (by rw [Category.id_comp])

private theorem normalizedStalkIso_derived {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S) :
    (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso (normalizedStalkIso t) =
      derivedGeometricPointStalkIso t := by
  unfold normalizedStalkIso
  rw [CategoryTheory.Functor.mapNat_transport]
  rfl

private theorem stalk_pasting {S T : Scheme.{u}} (g : T ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (M : _root_.DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (derivedPullbackStalkIso g t).hom.app M ≫
      (derivedGeometricPointStalkIso (t ≫ g)).inv.app M ≫
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.mapDerivedCategoryPlus.map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} t g).hom.app M) =
    (derivedGeometricPointStalkIso t).inv.app
      ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlus.obj M) := by
  let F := upperStar AddCommGrpCat.{u + 1} g
  let G := upperStar AddCommGrpCat.{u + 1} t
  let H := (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber
    (A := AddCommGrpCat.{u + 1})
  let L := upperStar AddCommGrpCat.{u + 1} (t ≫ g)
  let S := (Scheme.pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})
  let T := (Scheme.pointSmallEtale (t ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})
  let a := upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} g t
  let b := normalizedStalkIso t
  let c := normalizedStalkIso (t ≫ g)
  let d := upperStarComp AddCommGrpCat.{u + 1} t g
  have hq (Q : Sheaf _ _) : a.inv.app Q ≫ b.inv.app (F.obj Q) =
      c.inv.app Q ≫ H.map (d.hom.app Q) := by
    simpa only [a, b, c, normalizedStalkIso, Iso.trans_inv, NatTrans.comp_app,
      eqToIso.inv, eqToHom_app, Category.id_comp, eqToHom_refl, Category.id_comp]
      using stalk_pasting_underived g t Q
  have h := CategoryTheory.Functor.comparison_pasting F G H L S T a b c d hq M
  dsimp only [b, c] at h
  rw [normalizedStalkIso_derived, normalizedStalkIso_derived] at h
  apply (cancel_epi ((derivedPullbackStalkIso g t).inv.app M)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  exact h.symm

private theorem globalGermAt_identity {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S)
    (M : _root_.DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (derivedGlobalGermAt t).app M ≫ (derivedGeometricPointStalkIso t).inv.app M =
    (Functor.rightDerivedFunctorPlusNatTrans (pulledGlobalGerm t (𝟙 (Spec (.of Ω)))) ≫
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        ((upperStar AddCommGrpCat.{u + 1} t) ⋙
          (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber)).hom ≫
      (Functor.mapDerivedCategoryPlusCompIso _ _).hom).app M := by
  have hgen (s : Spec (.of Ω) ⟶ S) (hs : 𝟙 (Spec (.of Ω)) ≫ t = s) :
      (derivedGlobalGermAt s).app M ≫
        eqToHom (congrArg (fun y : Spec (.of Ω) ⟶ S ↦
          (Scheme.pointSmallEtale y).sheafFiber.mapDerivedCategoryPlus.obj M) hs.symm) ≫
        (Functor.mapDerivedCategoryPlusNatIso
          (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} t
            (𝟙 (Spec (.of Ω))))).inv.app M ≫
        (Functor.mapDerivedCategoryPlusCompIso
          (upperStar AddCommGrpCat.{u + 1} t)
          ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber
            (A := AddCommGrpCat.{u + 1}))).hom.app M =
      (Functor.rightDerivedFunctorPlusNatTrans
        (pulledGlobalGerm t (𝟙 (Spec (.of Ω)))) ≫
        (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
          ((upperStar AddCommGrpCat.{u + 1} t) ⋙
            (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber)).hom ≫
        (Functor.mapDerivedCategoryPlusCompIso _ _).hom).app M := by
    subst s
    simp only [eqToHom_refl, Category.id_comp]
    have h := NatTrans.congr_app (derive_germ_iso
      (Sheaf.Γ S.smallEtaleTopology AddCommGrpCat.{u + 1}) _ _
      (globalGerm (𝟙 (Spec (.of Ω)) ≫ t))
      (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} t
        (𝟙 (Spec (.of Ω))))) M
    simpa only [derivedGlobalGermAt, pulledGlobalGerm, NatTrans.comp_app,
      Category.assoc] using congrArg (fun z ↦ z ≫
        (Functor.mapDerivedCategoryPlusCompIso
          (upperStar AddCommGrpCat.{u + 1} t)
          ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber
            (A := AddCommGrpCat.{u + 1}))).hom.app M) h
  simpa only [derivedGeometricPointStalkIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, eqToIso.inv, eqToHom_app, Category.assoc] using
    hgen t (Category.id_comp t)

/-- The two-square fibre map agrees with the germ of the exchanged global sections
followed by restriction to the geometric fibre.
Source: Stacks Project, Tag 0GJV, the pullback-of-cohomology identification;
Tags 01F8 and 08J6, functoriality of derived exchange.
(blueprint: lem-weil-pbc-derived-fibre-restriction).

Proof: paste the exchange square with the geometric-point square. Horizontal pasting
expresses the outer exchange as pullback of the first exchange followed by the second,
with the inverse-image composition comparisons. The inverse-image stalk isomorphism
identifies the two stalk sources. Naturality of the global germ moves the first
exchange past that germ. Apply derivedGlobalGerm_exchange to the geometric-point square:
its right side is the derived inverse-image unit followed by Leray and the target germ.
The latter is invertible on the geometric base, so it cancels the inverse target germ
in etaleDerivedFiberMap. The remaining composite is etaleDerivedRestriction of the
fibre inclusion. Naturality of Leray gives the displayed order of the factors.
No exactness of sections on the base or strict-local hypothesis is used. -/
theorem derivedFiberMap_restriction
    {X X' S T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
    (g : T ⟶ S) (p : X' ⟶ X) (sq : IsPullback p f' f g)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (derivedGlobalGermAt t).app
        ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlus.obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj K)) ≫
      (derivedPullbackStalkIso g t).hom.app
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj K) ≫
      etaleDerivedFiberMap
        ((IsPullback.of_hasPullback f' t).paste_horiz sq).toCommSq K ≫
      (Sheaf.Γ (pullback f' t).smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} (pullback.fst f' t) p).hom.app K) =
    (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K) ≫
      (etaleLerayPlus f').hom.app _ ≫
      etaleDerivedRestriction (pullback.fst f' t)
        ((upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategoryPlus.obj K)  := by
  let B := AddCommGrpCat.{u + 1}
  let i := pullback.fst f' t
  let q := pullback.snd f' t
  let P := (upperStar B p).mapDerivedCategoryPlus
  let F := ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber
    (A := B)).mapDerivedCategoryPlus
  let H := (Sheaf.Γ (pullback f' t).smallEtaleTopology B).rightDerivedFunctorPlus
  let R := (lowerStar B f).rightDerivedFunctorPlus.obj K
  let c := (upperStarCompDerivedPlus B i p).hom.app K
  let e := derivedGlobalGerm q (𝟙 (Spec (.of Ω)))
  let := isIso_globalGerm_identity Ω
  let := isIso_derivedGlobalGerm q (𝟙 (Spec (.of Ω)))
  have hpaste := NatTrans.congr_app
    (derivedBaseChangeMapPlus_paste_horiz B sq.toCommSq
      (IsPullback.of_hasPullback f' t).toCommSq
      ((IsPullback.of_hasPullback f' t).paste_horiz sq).toCommSq) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    ] at hpaste
  have hn := (asIso e).inv.naturality c
  dsimp only [Functor.comp_map] at hn
  have he := derivedGlobalGerm_exchange f' q t i
    (IsPullback.of_hasPullback f' t) (𝟙 (Spec (.of Ω))) (P.obj K)
  have hfibre :
      etaleDerivedFiberMap
          ((IsPullback.of_hasPullback f' t).paste_horiz sq).toCommSq K ≫ H.map c =
        (derivedGeometricPointStalkIso (t ≫ g)).inv.app R ≫
          F.map ((upperStarCompDerivedPlus B t g).hom.app R) ≫
          F.map ((upperStar B t).mapDerivedCategoryPlus.map
            ((derivedBaseChangeMapPlus B sq.toCommSq).app K)) ≫
          F.map ((derivedBaseChangeMapPlus B
            (IsPullback.of_hasPullback f' t).toCommSq).app (P.obj K)) ≫
          inv (e.app _) := by
    dsimp only [etaleDerivedFiberMap]
    change (_ ≫ F.map _ ≫ inv (e.app _)) ≫ H.map c = _
    have hn' : inv (e.app _) ≫ H.map c =
        F.map ((lowerStar B q).rightDerivedFunctorPlus.map c) ≫ inv (e.app _) := by
      simpa only [e, c, H, F, Functor.comp_map, Iso.app_inv, asIso_inv,
        NatIso.isIso_inv_app] using hn.symm
    rw [Category.assoc, Category.assoc, hn']
    rw [← Category.assoc (F.map _) (F.map _), ← F.map_comp, hpaste]
    simp only [Functor.map_comp, Category.assoc]
    have hc : F.map ((lowerStar B q).rightDerivedFunctorPlus.map
          ((upperStarCompDerivedPlus B i p).inv.app K)) ≫
        F.map ((lowerStar B q).rightDerivedFunctorPlus.map c) = 𝟙 _ := by
      rw [← F.map_comp, ← Functor.map_comp]
      simp only [c, Iso.inv_hom_id_app]
      rw [(lowerStar B q).rightDerivedFunctorPlus.map_id, F.map_id]
    erw [reassoc_of% hc]
    dsimp only [rightDerivedLowerStarPlus]
    rfl
  dsimp only [rightDerivedLowerStarPlus]
  change (derivedGlobalGermAt t).app _ ≫ _ ≫ _ ≫ H.map c = _
  rw [hfibre]
  erw [reassoc_of% stalk_pasting g t R]
  have hg : (derivedPulledGlobalGerm f' t (𝟙 (Spec (.of Ω)))).app (P.obj K) =
      (etaleLerayPlus f').inv.app (P.obj K) ≫
        (derivedGlobalGermAt t).app
          ((lowerStar B f').rightDerivedFunctorPlus.obj (P.obj K)) ≫
        (derivedGeometricPointStalkIso t).inv.app
          ((lowerStar B f').rightDerivedFunctorPlus.obj (P.obj K)) := by
    have h := congrArg (fun z ↦ (etaleLerayPlus f').inv.app (P.obj K) ≫ z)
      (globalGermAt_identity t ((lowerStar B f').rightDerivedFunctorPlus.obj (P.obj K))).symm
    simpa only [derivedPulledGlobalGerm, etaleLerayPlus, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc] using h
  have heR : (derivedPulledGlobalGerm f' t (𝟙 (Spec (.of Ω)))).app (P.obj K) ≫
      F.map ((derivedBaseChangeMapPlus B
        (IsPullback.of_hasPullback f' t).toCommSq).app (P.obj K)) =
      etaleDerivedRestriction i (P.obj K) ≫ e.app _ := by
    exact he
  have hs := congrArg (fun z ↦
    (etaleLerayPlus f').hom.app (P.obj K) ≫ z ≫ inv (e.app _)) heR
  rw [hg] at hs
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at hs
  change (derivedGlobalGermAt t).app _ ≫
      (derivedGeometricPointStalkIso t).inv.app _ ≫
      F.map ((derivedBaseChangeMapPlus B
        (IsPullback.of_hasPullback f' t).toCommSq).app (P.obj K)) ≫ inv (e.app _) =
    (etaleLerayPlus f').hom.app (P.obj K) ≫
      etaleDerivedRestriction i (P.obj K) ≫ e.app _ ≫ inv (e.app _) at hs
  simp only [IsIso.hom_inv_id, Category.comp_id] at hs
  erw [← reassoc_of% ((derivedGeometricPointStalkIso t).inv.naturality
    ((derivedBaseChangeMapPlus B sq.toCommSq).app K))]
  erw [← reassoc_of% ((derivedGlobalGermAt t).naturality
    ((derivedBaseChangeMapPlus B sq.toCommSq).app K))]
  erw [hs]

end AlgebraicGeometry.Etale
