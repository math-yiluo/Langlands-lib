/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedGlobalGerm
public import WeilConjectures.SixFunctors.BaseChange.Derived

/-! # DerivedPulledGlobalGermFac

Source: Stacks Project, Tags 095T, 01F8 and 08J6.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale
open Scheme
attribute [local instance] GrothendieckTopology.Point.sheafFiber_additive
noncomputable local instance instAB5OfSizeAddCommGrpCat_derivedPulledGlobalGermFac
    : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
  AB5OfSize_shrink.{u, u, u + 1, u + 1} _

-- Keep the unused abbreviation R in the original statement unchanged.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency true in
-- Canonical homotopy comparison endpoints require repeated definitional equality checks.
/-- The source-side derived germ and exchange, precomposed with the global-sections
unit, are the localized underived source-side composite followed by the target units.
Source: Stacks Project, sites-cohomology.tex, Remark 08J6 and Lemma 0736;
cohomology.tex, Tag 01EZ.
(blueprint: lem-weil-pbc-derived-pulled-global-germ-fac)

Proof: Expand `derivedPulledGlobalGerm`. The Leray unit compatibility moves the
Γ_X unit across the inverse Leray comparison, giving the localized inverse terminal
section isomorphism followed by the composite Γ_Y and f_* units. Naturality moves the
f_* unit through the derived pulled germ. The defining compatibility of the right-derived
natural transformation with its units replaces the Γ_Y unit followed by the derived
pulled germ by its termwise map. The exact-functor comparison and composition comparison
replace the remaining derived unit by the two stalk/pullback factorization inverses.
Use `derivedBaseChangeMapPlus_fac_app` to replace the pullback of the f_* unit followed
by exchange by the termwise exchange, the f'_* unit and the g'^* comparison inverse.
Naturality of the stalk factorization collects the three target comparisons into c.
Functoriality of the homotopy quotient and localization combines the preceding maps
into the localization of `NatTrans.mapHomotopyCategoryPlus a`. -/
theorem derivedPulledGlobalGerm_fac
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (sq : CommSq g' f' f g)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y')
    (M : HomotopyCategory.Plus
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    let B := AddCommGrpCat.{u + 1}
    let F := lowerStar B f
    let F' := lowerStar B f'
    let G := upperStar B g
    let G' := upperStar B g'
    let R := lowerStar B g'
    let H := Sheaf.Γ X.smallEtaleTopology B
    let S := (pointSmallEtale t).sheafFiber
    let a : H ⟶ G' ⋙ F' ⋙ S :=
      (lowerStarCompGlobalSectionsIso B f).inv ≫
        Functor.whiskerLeft F (pulledGlobalGerm g t) ≫
        (Functor.associator F G S).inv ≫
        Functor.whiskerRight (baseChangeMap B sq) S ≫
        (Functor.associator G' F' S).hom
    let c := S.mapDerivedCategoryPlusFactorsh.inv.app
        (F'.mapHomotopyCategoryPlus.obj (G'.mapHomotopyCategoryPlus.obj M)) ≫
      S.mapDerivedCategoryPlus.map
        (F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj M)) ≫
      S.mapDerivedCategoryPlus.map (F'.rightDerivedFunctorPlus.map
        (G'.mapDerivedCategoryPlusFactorsh.inv.app M))
    H.rightDerivedFunctorPlusUnith.app M ≫
        (derivedPulledGlobalGerm f g t).app (DerivedCategory.Plus.Qh.obj M) ≫
        S.mapDerivedCategoryPlus.map
          ((derivedBaseChangeMapPlus B sq).app (DerivedCategory.Plus.Qh.obj M)) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus a).app M) ≫ c := by
  dsimp only
  let B := AddCommGrpCat.{u + 1}
  let F := lowerStar B f
  let J := Sheaf.Γ Y.smallEtaleTopology B
  let H := Sheaf.Γ X.smallEtaleTopology B
  let G := upperStar B g
  let S := (pointSmallEtale t).sheafFiber (A := B)
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction B f)
  let e := Functor.rightDerivedFunctorPlusCompIso' F J
    (lowerStarCompGlobalSectionsIso B f)
  have he : H.rightDerivedFunctorPlusUnith.app M ≫
      e.inv.app (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
        (lowerStarCompGlobalSectionsIso B f).inv).app M) ≫
      J.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj M) ≫
      J.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app M) := by
    change H.rightDerivedFunctorPlusUnith.app M ≫
      ((Functor.rightDerivedFunctorPlusNatTrans
        (lowerStarCompGlobalSectionsIso B f).inv).app (DerivedCategory.Plus.Qh.obj M) ≫
        (Functor.rightDerivedFunctorPlusCompIso F J).hom.app
          (DerivedCategory.Plus.Qh.obj M)) = _
    rw [Functor.rightDerivedFunctorPlusNatTrans_app_assoc,
      Functor.rightDerivedFunctorPlusCompIso_fac_app,
      Functor.rightDerivedFunctorPlusCompUnit_app]
  let β := Functor.rightDerivedFunctorPlusNatTrans (pulledGlobalGerm g t) ≫
    (G ⋙ S).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom ≫
    (Functor.mapDerivedCategoryPlusCompIso G S).hom
  set_option backward.isDefEq.respectTransparency false in
  have hβ (K : HomotopyCategory.Plus (Sheaf Y.smallEtaleTopology B)) :
      J.rightDerivedFunctorPlusUnith.app K ≫ β.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (pulledGlobalGerm g t)).app K) ≫
      S.mapDerivedCategoryPlusFactorsh.inv.app (G.mapHomotopyCategoryPlus.obj K) ≫
      S.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.inv.app K) := by
    dsimp only [β]
    simp only [NatTrans.comp_app]
    rw [Functor.rightDerivedFunctorPlusNatTrans_app_assoc]
    have hex := NatTrans.congr_app
      (G ⋙ S).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hex
    rw [reassoc_of% hex]
    have hc := Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh G S K
    rw [← cancel_mono (S.mapDerivedCategoryPlus.map
      (G.mapDerivedCategoryPlusFactorsh.hom.app K))]
    rw [← cancel_mono (S.mapDerivedCategoryPlusFactorsh.hom.app
      (G.mapHomotopyCategoryPlus.obj K))]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [hc]
    simp
    rfl
  have hnat := β.naturality (F.rightDerivedFunctorPlusUnith.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  set_option backward.isDefEq.respectTransparency false in
    change H.rightDerivedFunctorPlusUnith.app M ≫
      (e.inv.app (DerivedCategory.Plus.Qh.obj M) ≫
        β.app (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj M))) ≫
      S.mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus B sq).app (DerivedCategory.Plus.Qh.obj M)) = _
    simp only [Category.assoc]
    erw [reassoc_of% he]
    erw [reassoc_of% hnat, reassoc_of% hβ]
    simp only [← Functor.map_comp]
    rw [derivedBaseChangeMapPlus_fac_app B sq M]
    erw [Iso.inv_hom_id_app_assoc G.mapDerivedCategoryPlusFactorsh
      (F.mapHomotopyCategoryPlus.obj M)]
    simp only [Functor.map_comp]
    have hs := S.mapDerivedCategoryPlusFactorsh.inv.naturality
      ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap B sq)).app M)
    dsimp only [Functor.comp_obj, Functor.comp_map] at hs
    erw [← reassoc_of% hs]
    have ha :
        (lowerStarCompGlobalSectionsIso B f).inv ≫
          Functor.whiskerLeft F (pulledGlobalGerm g t) ≫
          (Functor.associator F G S).inv ≫
          Functor.whiskerRight (baseChangeMap B sq) S ≫
          (Functor.associator (upperStar B g') (lowerStar B f') S).hom =
        (lowerStarCompGlobalSectionsIso B f).inv ≫
          Functor.whiskerLeft F (pulledGlobalGerm g t) ≫
          Functor.whiskerRight (baseChangeMap B sq) S := by
      ext K : 2
      simp only [NatTrans.comp_app, Functor.associator_inv_app,
        Functor.associator_hom_app, Category.comp_id]
      erw [Category.id_comp]
    erw [ha]
    simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
      Functor.map_comp, Category.assoc]
    rfl

end AlgebraicGeometry.Etale
