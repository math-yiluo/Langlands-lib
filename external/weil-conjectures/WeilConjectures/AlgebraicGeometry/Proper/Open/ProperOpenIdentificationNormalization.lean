/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareSupplement
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc

/-!
# Unit normalization of the proper/open restriction identification

## References

* Stacks Project, More on Etale Cohomology, Tags 0F7B and 0F7I
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem homotopy_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {J : C ⥤ D} {U : D ⥤ C} [J.Additive] [U.Additive] (a : J ⊣ U)
    (K : HomotopyCategory.Plus C) :
    a.mapHomotopyCategoryPlus.unit.app K =
      (NatTrans.mapHomotopyCategoryPlus a.unit).app K := by
  apply (HomotopyCategory.Plus.ι C).map_injective
  rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app,
    NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  have hu (Z : HomotopyCategory C (ComplexShape.up ℤ)) :
      (a.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app Z =
        (NatTrans.mapHomotopyCategory a.unit (ComplexShape.up ℤ)).app Z := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    congr 1
  exact hu K.obj

private theorem localized_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {J : C ⥤ D} {U : D ⥤ C} [J.Additive] [U.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (a : J ⊣ U) [IsIso a.unit]
    (η : 𝟭 (DerivedCategory.Plus C) ⟶ J.mapDerivedCategoryPlus ⋙ U.mapDerivedCategoryPlus)
    (hη : ∀ K : HomotopyCategory.Plus C,
      η.app (DerivedCategory.Plus.Qh.obj K) ≫
        U.mapDerivedCategoryPlus.map (J.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        U.mapDerivedCategoryPlusFactorsh.hom.app (J.mapHomotopyCategoryPlus.obj K) =
      DerivedCategory.Plus.Qh.map (a.mapHomotopyCategoryPlus.unit.app K)) :
    η = (Functor.mapDerivedCategoryPlusIdIso C).inv ≫
      (Functor.mapDerivedCategoryPlusNatIso (asIso a.unit)).hom ≫
      (Functor.mapDerivedCategoryPlusCompIso J U).hom := by
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)
  intro K
  simp only [NatTrans.comp_app]
  apply (cancel_mono (U.mapDerivedCategoryPlus.map
    (J.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      U.mapDerivedCategoryPlusFactorsh.hom.app (J.mapHomotopyCategoryPlus.obj K))).mp
  rw [Category.assoc, hη,
    Category.assoc, Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  rw [← Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh,
    Iso.inv_hom_id_app_assoc]
  exact congrArg DerivedCategory.Plus.Qh.map (homotopy_unit a K)

private theorem inverse_unit_square
    {D E : Type*} [Category D] [Category E]
    (U : D ⥤ E) {W : E} {Y Z : D} (a : W ⟶ U.obj Y)
    (v : Y ≅ Z) (b : W ⟶ U.obj Z) (h : a ≫ U.map v.hom = b) :
    b ≫ U.map v.inv = a := by
  rw [← h, Category.assoc, ← U.map_comp, v.hom_inv_id, U.map_id, Category.comp_id]

private theorem localized_square_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    (J : C ⥤ D) (S : D ⥤ C) (J' : C' ⥤ D') (S' : D' ⥤ C')
    (H : C ⥤ C') (G : D ⥤ D')
    [J.Additive] [S.Additive] [J'.Additive] [S'.Additive] [H.Additive] [G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    [PreservesFiniteLimits S'] [PreservesFiniteColimits S']
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (ν : 𝟭 C ⟶ J ⋙ S) (ν' : 𝟭 C' ⟶ J' ⋙ S')
    (η : 𝟭 (DerivedCategory.Plus C) ⟶ J.mapDerivedCategoryPlus ⋙ S.mapDerivedCategoryPlus)
    (η' : 𝟭 (DerivedCategory.Plus C') ⟶ J'.mapDerivedCategoryPlus ⋙ S'.mapDerivedCategoryPlus)
    (ha : ∀ K, η.app (DerivedCategory.Plus.Qh.obj K) ≫
      S.mapDerivedCategoryPlus.map (J.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      S.mapDerivedCategoryPlusFactorsh.hom.app (J.mapHomotopyCategoryPlus.obj K) =
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus ν).app K))
    (hb : ∀ K, η'.app (DerivedCategory.Plus.Qh.obj K) ≫
      S'.mapDerivedCategoryPlus.map (J'.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      S'.mapDerivedCategoryPlusFactorsh.hom.app (J'.mapHomotopyCategoryPlus.obj K) =
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus ν').app K))
    (q : J ⋙ G ≅ H ⋙ J') (t : S ⋙ H ≅ G ⋙ S')
    (ed : J.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ≅
      H.mapDerivedCategoryPlus ⋙ J'.mapDerivedCategoryPlus)
    (td : S.mapDerivedCategoryPlus ⋙ H.mapDerivedCategoryPlus ≅
      G.mapDerivedCategoryPlus ⋙ S'.mapDerivedCategoryPlus)
    (he : ∀ N, ed.hom.app (DerivedCategory.Plus.Qh.obj N) ≫
      J'.mapDerivedCategoryPlus.map (H.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
      J'.mapDerivedCategoryPlusFactorsh.hom.app (H.mapHomotopyCategoryPlus.obj N) =
        G.mapDerivedCategoryPlus.map (J.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        G.mapDerivedCategoryPlusFactorsh.hom.app (J.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus q.hom).app N))
    (ht : ∀ N, td.hom.app (DerivedCategory.Plus.Qh.obj N) ≫
      S'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
      S'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj N) =
        H.mapDerivedCategoryPlus.map (S.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        H.mapDerivedCategoryPlusFactorsh.hom.app (S.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus t.hom).app N))
    (hq : ∀ F, H.map (ν.app F) ≫ t.hom.app (J.obj F) ≫ S'.map (q.hom.app F) =
      ν'.app (H.obj F))
    (K : DerivedCategory.Plus C) :
    H.mapDerivedCategoryPlus.map (η.app K) ≫
      td.hom.app (J.mapDerivedCategoryPlus.obj K) ≫
      S'.mapDerivedCategoryPlus.map (ed.hom.app K) =
      η'.app (H.mapDerivedCategoryPlus.obj K) := by
  let τ := Functor.whiskerRight η H.mapDerivedCategoryPlus ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft J.mapDerivedCategoryPlus td.hom ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ed.hom S'.mapDerivedCategoryPlus ≫
    (Functor.associator _ _ _).hom
  have hτ : τ = Functor.whiskerLeft H.mapDerivedCategoryPlus η' := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)
    intro N
    simp only [τ, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    apply (cancel_mono (S'.mapDerivedCategoryPlus.map
      (J'.mapDerivedCategoryPlus.map (H.mapDerivedCategoryPlusFactorsh.hom.app N)) ≫
      S'.mapDerivedCategoryPlus.map
        (J'.mapDerivedCategoryPlusFactorsh.hom.app (H.mapHomotopyCategoryPlus.obj N)) ≫
      S'.mapDerivedCategoryPlusFactorsh.hom.app
        (J'.mapHomotopyCategoryPlus.obj (H.mapHomotopyCategoryPlus.obj N)))).mp
    simp only [Category.assoc]
    rw [← S'.mapDerivedCategoryPlus.map_comp_assoc,
      ← S'.mapDerivedCategoryPlus.map_comp_assoc, Category.assoc, he]
    simp only [Functor.map_comp, Category.assoc]
    have hnq := S'.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus q.hom).app N)
    dsimp only [Functor.comp_map] at hnq
    erw [hnq]
    have htn := td.hom.naturality (J.mapDerivedCategoryPlusFactorsh.hom.app N)
    simp only [Functor.comp_map] at htn
    rw [← reassoc_of% htn]
    have htf := ht (J.mapHomotopyCategoryPlus.obj N)
    slice_lhs 3 5 => exact htf
    simp only [Category.assoc]
    have han := H.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus ν).app N)
    have hbn := η'.naturality (H.mapDerivedCategoryPlusFactorsh.hom.app N)
    simp only [Functor.comp_map, Functor.id_map] at han hbn
    rw [← reassoc_of% hbn]
    slice_rhs 2 4 => exact hb (H.mapHomotopyCategoryPlus.obj N)
    slice_lhs 1 3 =>
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg H.mapDerivedCategoryPlus.map (ha N)
    slice_lhs 1 2 => exact han
    have hqh :
        H.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus ν).app N) ≫
          (NatTrans.mapHomotopyCategoryPlus t.hom).app (J.mapHomotopyCategoryPlus.obj N) ≫
          S'.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus q.hom).app N) =
        (NatTrans.mapHomotopyCategoryPlus ν').app (H.mapHomotopyCategoryPlus.obj N) := by
      have hnat : Functor.whiskerRight ν H ≫
          Functor.whiskerLeft J t.hom ≫ Functor.whiskerRight q.hom S' =
            Functor.whiskerLeft H ν' := by
        ext F
        simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_hom_app, Functor.associator_inv_app,
          Category.id_comp, Category.comp_id] using hq F
      have hh := NatTrans.congr_app (congrArg NatTrans.mapHomotopyCategoryPlus hnat) N
      simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app] at hh
      simpa only [NatTrans.mapHomotopyCategoryPlus_whiskerRight_app,
        NatTrans.mapHomotopyCategoryPlus_whiskerLeft_app] using hh
    simp only [Category.assoc]
    apply congrArg (fun z ↦ H.mapDerivedCategoryPlusFactorsh.hom.app N ≫ z)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Plus.Qh.map hqh
  simpa only [τ, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using NatTrans.congr_app hτ K

private theorem normalized_unit_fac
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {J : C ⥤ D} {S : D ⥤ C} [J.Additive] [S.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (ν : 𝟭 C ⟶ J ⋙ S) [IsIso ν]
    (η : 𝟭 (DerivedCategory.Plus C) ⟶ J.mapDerivedCategoryPlus ⋙ S.mapDerivedCategoryPlus)
    (hη : η = (Functor.mapDerivedCategoryPlusIdIso C).inv ≫
      (Functor.mapDerivedCategoryPlusNatIso (asIso ν)).hom ≫
      (Functor.mapDerivedCategoryPlusCompIso J S).hom)
    (K : HomotopyCategory.Plus C) :
    η.app (DerivedCategory.Plus.Qh.obj K) ≫
      S.mapDerivedCategoryPlus.map (J.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      S.mapDerivedCategoryPlusFactorsh.hom.app (J.mapHomotopyCategoryPlus.obj K) =
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus ν).app K) := by
  rw [hη]
  simp only [NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  rw [← Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh,
    Iso.inv_hom_id_app_assoc]
  rfl

private theorem localized_square_unit_forward
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    (J : C ⥤ D) (S : D ⥤ C) (J' : C' ⥤ D') (S' : D' ⥤ C')
    (H : C ⥤ C') (G : D ⥤ D')
    [J.Additive] [S.Additive] [J'.Additive] [S'.Additive] [H.Additive] [G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    [PreservesFiniteLimits S'] [PreservesFiniteColimits S']
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (ν : 𝟭 C ⟶ J ⋙ S) (ν' : 𝟭 C' ⟶ J' ⋙ S')
    (η : 𝟭 (DerivedCategory.Plus C) ⟶ J.mapDerivedCategoryPlus ⋙ S.mapDerivedCategoryPlus)
    (η' : 𝟭 (DerivedCategory.Plus C') ⟶ J'.mapDerivedCategoryPlus ⋙ S'.mapDerivedCategoryPlus)
    [IsIso ν] [IsIso ν']
    (hη : η = (Functor.mapDerivedCategoryPlusIdIso C).inv ≫
      (Functor.mapDerivedCategoryPlusNatIso (asIso ν)).hom ≫
      (Functor.mapDerivedCategoryPlusCompIso J S).hom)
    (hη' : η' = (Functor.mapDerivedCategoryPlusIdIso C').inv ≫
      (Functor.mapDerivedCategoryPlusNatIso (asIso ν')).hom ≫
      (Functor.mapDerivedCategoryPlusCompIso J' S').hom)
    (q : J ⋙ G ≅ H ⋙ J') (t : S ⋙ H ≅ G ⋙ S')
    (ed : J.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ≅
      H.mapDerivedCategoryPlus ⋙ J'.mapDerivedCategoryPlus)
    (td : S.mapDerivedCategoryPlus ⋙ H.mapDerivedCategoryPlus ≅
      G.mapDerivedCategoryPlus ⋙ S'.mapDerivedCategoryPlus)
    (he : ∀ N, ed.hom.app (DerivedCategory.Plus.Qh.obj N) ≫
      J'.mapDerivedCategoryPlus.map (H.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
      J'.mapDerivedCategoryPlusFactorsh.hom.app (H.mapHomotopyCategoryPlus.obj N) =
        G.mapDerivedCategoryPlus.map (J.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        G.mapDerivedCategoryPlusFactorsh.hom.app (J.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus q.hom).app N))
    (ht : ∀ N, td.hom.app (DerivedCategory.Plus.Qh.obj N) ≫
      S'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
      S'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj N) =
        H.mapDerivedCategoryPlus.map (S.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        H.mapDerivedCategoryPlusFactorsh.hom.app (S.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus t.hom).app N))
    (hq : ∀ F, ν'.app (H.obj F) ≫ S'.map (q.inv.app F) =
      H.map (ν.app F) ≫ t.hom.app (J.obj F))
    (K : DerivedCategory.Plus C) :
    H.mapDerivedCategoryPlus.map (η.app K) ≫
      td.hom.app (J.mapDerivedCategoryPlus.obj K) ≫
      S'.mapDerivedCategoryPlus.map (ed.hom.app K) =
      η'.app (H.mapDerivedCategoryPlus.obj K) := by
  refine localized_square_unit J S J' S' H G ν ν' η η'
    (normalized_unit_fac ν η hη) (normalized_unit_fac ν' η' hη') q t ed td he ht ?_ K
  intro F
  simpa only [Iso.app_inv, Iso.symm_inv, Category.assoc] using
    inverse_unit_square S' _ (q.symm.app F) _ (hq F)

private theorem section_cancel
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} {U : D ⥤ C} {S : C ⥤ D}
    (a : L ⊣ R) (b : U ⊣ S) (ρ : S ⋙ R ≅ 𝟭 C) (e : 𝟭 C ≅ L ⋙ U)
    (hn : ∀ Z, (a.comp b).unit.app Z ≫ ρ.hom.app (U.obj (L.obj Z)) = e.hom.app Z)
    {Z : C} {W : D} (r : Z ⟶ R.obj W) :
    r ≫ R.map (b.unit.app W) ≫ ρ.hom.app (U.obj W) =
      e.hom.app Z ≫ U.map ((a.homEquiv Z W).symm r) := by
  let v := (a.homEquiv Z W).symm r
  have hr : r = a.unit.app Z ≫ R.map v := by
    exact ((a.homEquiv Z W).apply_symm_apply r).symm
  change r ≫ R.map (b.unit.app W) ≫ ρ.hom.app (U.obj W) = e.hom.app Z ≫ U.map v
  conv_lhs => rw [hr]
  have hbu := b.unit.naturality v
  simp only [Functor.id_map, Functor.comp_map] at hbu
  rw [Category.assoc, ← R.map_comp_assoc, hbu, R.map_comp, Category.assoc]
  have hρ := ρ.hom.naturality (U.map v)
  simp only [Functor.comp_map, Functor.id_map] at hρ
  rw [hρ]
  have hn' := hn Z
  rw [Adjunction.comp_unit_app] at hn'
  rw [← Category.assoc, ← Category.assoc, hn']

private theorem restriction_assembly
    {C D E : Type*} [Category C] [Category D] [Category E]
    {P : C ⥤ D} {R : D ⥤ C} {S : D ⥤ C} {T : C ⥤ D}
    (a : P ⊣ R) (b : S ⊣ T) (ρ : T ⋙ R ≅ 𝟭 C) (ι : 𝟭 C ≅ P ⋙ S)
    (hn : ∀ Z, (a.comp b).unit.app Z ≫ ρ.hom.app (S.obj (P.obj Z)) = ι.hom.app Z)
    (U : E ⥤ C) (B : E ⥤ D) (k : U ≅ B ⋙ S)
    {K Z : C} {M : E} {N : D} (e : B.obj M ≅ N) (c : R.obj N ≅ K)
    (η : K ⟶ U.obj M) (η' : K ⟶ S.obj N)
    (hη : η ≫ k.hom.app M ≫ S.map e.hom = η')
    (hc : c.hom ≫ η' = R.map (b.unit.app N) ≫ ρ.hom.app (S.obj N))
    (r : Z ⟶ R.obj (B.obj M)) :
    r ≫ R.map e.hom ≫ c.hom ≫ η ≫ k.hom.app M =
      ι.hom.app Z ≫ S.map ((a.homEquiv Z (B.obj M)).symm r) := by
  apply (cancel_mono (S.map e.hom)).mp
  simp only [Category.assoc]
  rw [hη, hc]
  have he := b.unit.naturality e.hom
  simp only [Functor.id_map, Functor.comp_map] at he
  rw [← R.map_comp_assoc, he, R.map_comp, Category.assoc]
  have hr := ρ.hom.naturality (S.map e.hom)
  simp only [Functor.comp_map, Functor.id_map] at hr
  rw [hr]
  simpa only [Category.assoc] using
    congrArg (fun z ↦ z ≫ S.map e.hom) (section_cancel a b ρ ι hn r)

private theorem exact_unit_general (A : Type (u + 2)) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      A j).unit =
      (Functor.mapDerivedCategoryPlusIdIso
        (Sheaf U.smallEtaleTopology A)).inv ≫
        (Functor.mapDerivedCategoryPlusNatIso
          (asIso (openImmersionLowerShriekUpperStarAdjunction
            A j).unit)).hom ≫
        (Functor.mapDerivedCategoryPlusCompIso
          (openImmersionLowerShriek A j)
          (upperStar A j)).hom := by
  exact localized_unit (openImmersionLowerShriekUpperStarAdjunction
    A j) _
    (Adjunction.mapDerivedCategoryPlusAdjunction_unit_app_fac
      (openImmersionLowerShriekUpperStarAdjunction A j))

private theorem exact_unit (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) j).unit =
      (Functor.mapDerivedCategoryPlusIdIso
        (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))).inv ≫
        (Functor.mapDerivedCategoryPlusNatIso
          (asIso (openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} Λ) j).unit)).hom ≫
        (Functor.mapDerivedCategoryPlusCompIso
          (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)
          (upperStar (ModuleCat.{u + 1} Λ) j)).hom := by
  exact exact_unit_general (ModuleCat.{u + 1} Λ) j

private theorem exact_square_fac
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    (R : C ⥤ D) (G : D ⥤ F) (L : C ⥤ E) (S : E ⥤ F)
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (q : R ⋙ G ≅ L ⋙ S)
    (e : R.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ≅
      L.mapDerivedCategoryPlus ⋙ S.mapDerivedCategoryPlus)
    (he : e = Functor.mapDerivedCategoryPlusSquareIso R G L S q)
    (K : HomotopyCategory.Plus C) :
    e.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
      S.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      S.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) =
        G.mapDerivedCategoryPlus.map (R.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        G.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus q.hom).app K) := by
  subst e
  exact Functor.mapDerivedCategoryPlusSquareIso_fac R G L S q K

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryPlus
  openImmersionLowerShriekBaseChangeMap
  upperStar lowerStar openImmersionLowerShriek openImmersionLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
  CategoryTheory.Adjunction.mapDerivedCategoryPlusAdjunction
  pullbackSquareComparison squareUpperStarIso
  CategoryTheory.Functor.mapDerivedCategoryPlusSquareIso
  extensionZeroBaseChangeDerivedPlusIso

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxRecDepth 800 in
private theorem open_bc_unit_general (A : Type (u + 2)) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g)
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology A)) :
    (upperStar A gU).mapDerivedCategoryPlus.map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          A j).unit.app K) ≫
      (pullbackSquareComparison A sq.toCommSq.flip).hom.app
        ((openImmersionLowerShriek A j).mapDerivedCategoryPlus.obj K) ≫
      (upperStar A j').mapDerivedCategoryPlus.map
        ((Functor.mapDerivedCategoryPlusSquareIso
          (openImmersionLowerShriek A j) (upperStar A g)
          (upperStar A gU) (openImmersionLowerShriek A j')
          (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A sq)).symm).hom.app K) =
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      A j').unit.app
        ((upperStar A gU).mapDerivedCategoryPlus.obj K) := by
  let J := openImmersionLowerShriek A j
  let S := upperStar A j
  let J' := openImmersionLowerShriek A j'
  let S' := upperStar A j'
  let H := upperStar A gU
  let G := upperStar A g
  let q : J ⋙ G ≅ H ⋙ J' :=
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A sq)).symm
  let t : S ⋙ H ≅ G ⋙ S' := squareUpperStarIso A sq.toCommSq.flip
  have hq := unit_map_openImmersionLowerShriekBaseChangeMap_app A sq.toCommSq
  have ht := pullbackSquareComparison_hom_app_factorsh A sq.toCommSq.flip
  have he := exact_square_fac J G H J' q
    (Functor.mapDerivedCategoryPlusSquareIso
          (openImmersionLowerShriek A j) (upperStar A g)
          (upperStar A gU) (openImmersionLowerShriek A j')
          (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A sq)).symm) (by
      rfl)
  have hpartial := localized_square_unit_forward J S J' S' H G
    (openImmersionLowerShriekUpperStarAdjunction A j).unit
    (openImmersionLowerShriekUpperStarAdjunction A j').unit
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j).unit
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j').unit
  have hfirst := hpartial (exact_unit_general A j)
  have hsecond := hfirst (exact_unit_general A j')
  have hqarg := hsecond q
  have htarg := hqarg t
  have hearg := htarg (Functor.mapDerivedCategoryPlusSquareIso
          (openImmersionLowerShriek A j) (upperStar A g)
          (upperStar A gU) (openImmersionLowerShriek A j')
          (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A sq)).symm)
  have hthird := hearg (pullbackSquareComparison A sq.toCommSq.flip)
  have hfourth := hthird he
  have hfifth := hfourth (fun N ↦ by
    dsimp only [J, S, J', S', H, G, t]
    exact ht N)
  have hfinal := hfifth hq K
  exact hfinal

private theorem open_bc_unit (Λ : Type (u + 1)) [CommRing Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g)
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (upperStar (ModuleCat.{u + 1} Λ) gU).mapDerivedCategoryPlus.map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} Λ) j).unit.app K) ≫
      (pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K) ≫
      (upperStar (ModuleCat.{u + 1} Λ) j').mapDerivedCategoryPlus.map
        ((extensionZeroBaseChangeDerivedPlusIso Λ sq).hom.app K) =
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) j').unit.app
        ((upperStar (ModuleCat.{u + 1} Λ) gU).mapDerivedCategoryPlus.obj K) := by
  have hu := open_bc_unit_general (ModuleCat.{u + 1} Λ) sq K
  unfold Functor.mapDerivedCategoryPlusSquareIso at hu
  unfold extensionZeroBaseChangeDerivedPlusIso
  exact hu

private theorem restricted_open_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X V T : Scheme.{u}} (s : X ⟶ V) (b : V ⟶ T) (j : X ⟶ T)
    [IsOpenImmersion s] [IsOpenImmersion j]
    (sq : IsPullback (𝟙 X) s j b)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    let A := ModuleCat.{u + 1} Λ
    let e := (extensionZeroBaseChangeDerivedPlusIso Λ sq).app K ≪≫
      (openImmersionLowerShriek A s).mapDerivedCategoryPlus.mapIso
        ((upperStarIdDerivedPlus A X).app K)
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j).unit.app K ≫
      (upperStarCompDerivedPlus A s b j
        (by simpa only [Category.id_comp] using sq.w)).hom.app
          ((openImmersionLowerShriek A j).mapDerivedCategoryPlus.obj K) ≫
      (upperStar A s).mapDerivedCategoryPlus.map e.hom =
        (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A s).unit.app K := by
  let A := ModuleCat.{u + 1} Λ
  have hj : j = s ≫ b := by simpa only [Category.id_comp] using sq.w
  subst j
  have ht := pullbackSquareComparison_eq A sq.toCommSq.flip
  let M := (openImmersionLowerShriek A (s ≫ b)).mapDerivedCategoryPlus.obj K
  have hid : (upperStarCompDerivedPlus A (𝟙 X) (s ≫ b) (s ≫ b)
      (Category.id_comp (s ≫ b)).symm).inv.app M =
      (upperStarIdDerivedPlus A X).hom.app
        ((upperStar A (s ≫ b)).mapDerivedCategoryPlus.obj M) := by
    apply (cancel_epi ((upperStarCompDerivedPlus A (𝟙 X) (s ≫ b) (s ≫ b)
      (Category.id_comp (s ≫ b)).symm).hom.app M)).mp
    rw [Iso.hom_inv_id_app]
    exact (NatTrans.congr_app (upperStarCompDerivedPlus_id_left A (s ≫ b)) M).symm
  have hu := open_bc_unit Λ sq K
  have hn := (upperStarIdDerivedPlus A X).hom.naturality
    ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A (s ≫ b)).unit.app K)
  have hs := (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A s).unit.naturality
    ((upperStarIdDerivedPlus A X).hom.app K)
  dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  dsimp only [A, Functor.comp_obj, Functor.id_obj] at *
  rw [Functor.map_comp]
  apply (cancel_epi ((upperStarIdDerivedPlus A X).hom.app K)).mp
  simp only [Functor.id_map] at hn
  rw [← reassoc_of% hn]
  rw [ht] at hu
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at hu
  rw [hid] at hu
  rw [reassoc_of% hu]
  simp only [Functor.comp_map, Functor.id_map] at hs
  exact hs.symm

private theorem section_unit (A : Type (u + 2)) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    {X V : Scheme.{u}} (s : X ⟶ V) (p : V ⟶ X) (hsp : s ≫ p = 𝟙 X)
    (Z : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    haveI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction A s)
    (((upperStarLowerStarAdjunction A p).derivedPlus).comp
        ((upperStarLowerStarAdjunction A s).derivedPlus)).unit.app Z ≫
      ((Functor.rightDerivedFunctorPlusCompIso'
        (lowerStar A s) (lowerStar A p)
        (lowerStarComp A s p (𝟙 X) hsp.symm)) ≪≫
        lowerStarIdDerivedPlus A X).hom.app
          ((upperStar A s).mapDerivedCategoryPlus.obj
            ((upperStar A p).mapDerivedCategoryPlus.obj Z)) =
      ((upperStarIdDerivedPlus A X).symm ≪≫
        upperStarCompDerivedPlus A s p (𝟙 X) hsp.symm).hom.app Z := by
  let aid := (upperStarLowerStarAdjunction A (𝟙 X)).derivedPlus
  let Uid := (upperStar A (𝟙 X)).mapDerivedCategoryPlus
  let Rid := (lowerStar A (𝟙 X)).rightDerivedFunctorPlus
  let d := lowerStarIdDerivedPlus A X
  let e := upperStarIdDerivedPlus A X
  have hi : aid.unit.app Z ≫ d.hom.app (Uid.obj Z) = e.inv.app Z := by
    apply (cancel_mono (e.hom.app Z)).mp
    have hn := d.hom.naturality (e.hom.app Z)
    simp only [Functor.id_map] at hn
    rw [Category.assoc, ← hn]
    have hu := NatTrans.congr_app (derivedPlus_unit_comp_upperStarIdDerivedPlus A X) Z
    simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hu
    rw [← Category.assoc, hu, Iso.inv_hom_id_app]
    dsimp only [d, Functor.id_obj]
    exact Iso.inv_hom_id_app _ Z
  have hc := derivedPlus_unit_comp_upperStarCompDerivedPlus A s p (𝟙 X) hsp.symm Z
  simp only [Adjunction.comp_unit_app, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  slice_lhs 1 3 => exact hc.symm
  have hn := d.hom.naturality
    ((upperStarCompDerivedPlus A s p (𝟙 X) hsp.symm).hom.app Z)
  simp only [Functor.id_map] at hn
  dsimp only [d, e, Uid, Rid, aid, Functor.comp_obj, Functor.id_obj] at *
  rw [Category.assoc, hn, ← Category.assoc, hi]
  rfl

private theorem section_square_coherence (A : Type (u + 2)) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    {X V T₁ T₂ : Scheme.{u}} (s : X ⟶ V) (p : V ⟶ X)
    (b : V ⟶ T₁) (f : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    (sp : s ≫ p = 𝟙 X) (sb : s ≫ b = j₁) (h : j₁ ≫ f = j₂)
    (sq : CommSq b p f j₂)
    (N : DerivedCategory.Plus (Sheaf T₂.smallEtaleTopology A)) :
    ((upperStarIdDerivedPlus A X).symm ≪≫
      upperStarCompDerivedPlus A s p (𝟙 X) sp.symm).hom.app
        ((upperStar A j₂).mapDerivedCategoryPlus.obj N) ≫
      (upperStar A s).mapDerivedCategoryPlus.map
        ((pullbackSquareComparison A sq).hom.app N) =
      (upperStarCompDerivedPlus A j₁ f j₂ h.symm).hom.app N ≫
        (upperStarCompDerivedPlus A s b j₁ sb.symm).hom.app
          ((upperStar A f).mapDerivedCategoryPlus.obj N) := by
  have h₁ := NatTrans.congr_app
    (upperStarCompDerivedPlus_assoc A s p j₂ (𝟙 X) (b ≫ f) j₂
      sp.symm sq.w (Category.id_comp j₂).symm) N
  have h₂ := NatTrans.congr_app
    (upperStarCompDerivedPlus_assoc A s b f j₁ (b ≫ f) j₂ sb.symm rfl h.symm) N
  have hi : (upperStarIdDerivedPlus A X).inv.app
      ((upperStar A j₂).mapDerivedCategoryPlus.obj N) =
      (upperStarCompDerivedPlus A (𝟙 X) j₂ j₂ (Category.id_comp j₂).symm).hom.app N := by
    apply (cancel_mono ((upperStarIdDerivedPlus A X).hom.app
      ((upperStar A j₂).mapDerivedCategoryPlus.obj N))).mp
    rw [Iso.inv_hom_id_app]
    exact (NatTrans.congr_app (upperStarCompDerivedPlus_id_left A j₂) N).symm
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h₁ h₂
  rw [pullbackSquareComparison_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [hi, ← Category.assoc, ← h₁]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  exact h₂

private theorem restriction_complete
    {C D E : Type*} [Category C] [Category D] [Category E]
    {P : C ⥤ D} {R : D ⥤ C} {S : D ⥤ C} {T : C ⥤ D}
    (a : P ⊣ R) (b : S ⊣ T) (ρ : T ⋙ R ≅ 𝟭 C) (ι : 𝟭 C ≅ P ⋙ S)
    (hn : ∀ Z, (a.comp b).unit.app Z ≫ ρ.hom.app (S.obj (P.obj Z)) = ι.hom.app Z)
    (U : E ⥤ C) (B : E ⥤ D) (k : U ≅ B ⋙ S)
    {K Z : C} {M : E} {N : D} (e : B.obj M ≅ N) (c : R.obj N ≅ K)
    (η : K ⟶ U.obj M) (η' : K ⟶ S.obj N)
    (hη : η ≫ k.hom.app M ≫ S.map e.hom = η')
    (hc : c.hom ≫ η' = R.map (b.unit.app N) ≫ ρ.hom.app (S.obj N))
    (r : Z ⟶ R.obj (B.obj M)) {Q : E} (v : Q ⟶ M) (w : Z ⟶ U.obj Q)
    (t : P.obj Z ⟶ B.obj Q)
    (hr : (a.homEquiv Z (B.obj M)).symm r = t ≫ B.map v)
    (hcoh : ι.hom.app Z ≫ S.map t = w ≫ k.hom.app Q) :
    (r ≫ R.map e.hom ≫ c.hom) ≫ η = w ≫ U.map v := by
  apply (Iso.cancel_iso_hom_right _ _ (k.app M)).mp
  change ((r ≫ R.map e.hom ≫ c.hom) ≫ η) ≫ k.hom.app M =
    (w ≫ U.map v) ≫ k.hom.app M
  simp only [Category.assoc]
  rw [restriction_assembly a b ρ ι hn U B k e c η η' hη hc r, hr, S.map_comp,
    ← Category.assoc, hcoh, Category.assoc]
  simpa only [Functor.comp_map] using
    congrArg (fun z ↦ w ≫ z) (k.hom.naturality v).symm

private theorem mate_transpose
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') {G : C ⥤ E} {H : D ⥤ F}
    (α : TwoSquare G L L' H) (M : D) :
    (b.homEquiv _ _).symm ((mateEquiv a b α).app M) =
      α.app (R.obj M) ≫ H.map (a.counit.app M) := by
  rw [Adjunction.homEquiv_counit]
  exact mateEquiv_counit a b α M

private theorem mate_transpose_eq
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') {G : C ⥤ E} {H : D ⥤ F}
    (α : TwoSquare G L L' H) (M : D) (r : G.obj (R.obj M) ⟶ R'.obj (H.obj M))
    (hr : r = (mateEquiv a b α).app M) :
    (b.homEquiv _ _).symm r = α.app (R.obj M) ≫ H.map (a.counit.app M) := by
  rw [hr]
  exact mate_transpose a b α M

private theorem exchange_transpose (A : Type (u + 2)) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    {X' X Y' Y : Scheme.{u}} {b : X' ⟶ X} {p : X' ⟶ Y'}
    {f : X ⟶ Y} {j : Y' ⟶ Y} (sq : CommSq b p f j)
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (((upperStarLowerStarAdjunction A p).derivedPlus).homEquiv _ _).symm
      ((derivedBaseChangeMapPlus A sq).app M) =
      (pullbackSquareComparison A sq).hom.app
        ((lowerStar A f).rightDerivedFunctorPlus.obj M) ≫
      (upperStar A b).mapDerivedCategoryPlus.map
        ((upperStarLowerStarAdjunction A f).derivedPlus.counit.app M) := by
  let α := TwoSquare.mk _ _ _ _ (pullbackSquareComparison A sq).hom
  exact mate_transpose_eq (upperStarLowerStarAdjunction A f).derivedPlus
    (upperStarLowerStarAdjunction A p).derivedPlus α M _
    ((congrArg (fun τ ↦ τ.app M)
      (baseChange_eq_derivedBaseChangeMapPlus A sq)).symm.trans
        (baseChange_app_eq_mateEquiv A sq M))

private theorem geometric_restriction (A : Type (u + 2)) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    {X V T₁ T₂ : Scheme.{u}} (s : X ⟶ V) (p : V ⟶ X)
    (b : V ⟶ T₁) (f : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    (sp : s ≫ p = 𝟙 X) (sb : s ≫ b = j₁) (h : j₁ ≫ f = j₂)
    (sq : CommSq b p f j₂)
    (M : DerivedCategory.Plus (Sheaf T₁.smallEtaleTopology A))
    (N : DerivedCategory.Plus (Sheaf V.smallEtaleTopology A))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))
    (e : (upperStar A b).mapDerivedCategoryPlus.obj M ≅ N)
    (c : (lowerStar A p).rightDerivedFunctorPlus.obj N ≅ K)
    (η : K ⟶ (upperStar A j₁).mapDerivedCategoryPlus.obj M)
    (η' : K ⟶ (upperStar A s).mapDerivedCategoryPlus.obj N) :
    haveI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction A s)
    let ρ := Functor.rightDerivedFunctorPlusCompIso' (lowerStar A s) (lowerStar A p)
      (lowerStarComp A s p (𝟙 X) sp.symm) ≪≫ lowerStarIdDerivedPlus A X
    η ≫ (upperStarCompDerivedPlus A s b j₁ sb.symm).hom.app M ≫
        (upperStar A s).mapDerivedCategoryPlus.map e.hom = η' →
    c.hom ≫ η' = (lowerStar A p).rightDerivedFunctorPlus.map
      ((upperStarLowerStarAdjunction A s).derivedPlus.unit.app N) ≫
      ρ.hom.app ((upperStar A s).mapDerivedCategoryPlus.obj N) →
    ((derivedBaseChangeMapPlus A sq).app M ≫
      (lowerStar A p).rightDerivedFunctorPlus.map e.hom ≫ c.hom) ≫ η =
    (upperStarCompDerivedPlus A j₁ f j₂ h.symm).hom.app
      ((lowerStar A f).rightDerivedFunctorPlus.obj M) ≫
      (upperStar A j₁).mapDerivedCategoryPlus.map
        ((upperStarLowerStarAdjunction A f).derivedPlus.counit.app M) := by
  dsimp only
  intro he hc
  let a := (upperStarLowerStarAdjunction A p).derivedPlus
  let a' := (upperStarLowerStarAdjunction A s).derivedPlus
  have : (lowerStar A s).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction A s)
  let ρ := Functor.rightDerivedFunctorPlusCompIso' (lowerStar A s) (lowerStar A p)
    (lowerStarComp A s p (𝟙 X) sp.symm) ≪≫ lowerStarIdDerivedPlus A X
  let ι := (upperStarIdDerivedPlus A X).symm ≪≫
    upperStarCompDerivedPlus A s p (𝟙 X) sp.symm
  exact restriction_complete a a' ρ ι (section_unit A s p sp)
    (upperStar A j₁).mapDerivedCategoryPlus (upperStar A b).mapDerivedCategoryPlus
    (upperStarCompDerivedPlus A s b j₁ sb.symm) e c η η' he hc
    ((derivedBaseChangeMapPlus A sq).app M)
    ((upperStarLowerStarAdjunction A f).derivedPlus.counit.app M)
    ((upperStarCompDerivedPlus A j₁ f j₂ h.symm).hom.app
      ((lowerStar A f).rightDerivedFunctorPlus.obj M))
    ((pullbackSquareComparison A sq).hom.app
      ((lowerStar A f).rightDerivedFunctorPlus.obj M))
    (exchange_transpose A sq M)
    (section_square_coherence A s p b f j₁ j₂ sp sb h sq
      ((lowerStar A f).rightDerivedFunctorPlus.obj M))

/-- The specified proper/open restriction identification is the canonical restriction map,
after identifying `K` with `j₁^* j₁! K` by the extension-by-zero unit. -/
theorem properOpenIdentificationOfCommRing_unit
    (Λ : Type (u + 1)) [CommRing Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (properOpenIdentificationOfCommRing Λ f j₁ j₂ h K).hom ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} Λ) j₁).unit.app K =
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j₁ f j₂ h.symm).hom.app
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)) ≫
        (upperStar (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus.counit.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj
              K)) := by
  let A := ModuleCat.{u + 1} Λ
  let s := properOpenSection f j₁ j₂ h
  let b := pullback.fst f j₂
  let p := pullback.snd f j₂
  let geom := properOpenSectionGeometry f j₁ j₂ h
  have : IsOpenImmersion s := geom.1
  have sp : s ≫ p = 𝟙 X := pullback.lift_snd _ _ _
  have sb : s ≫ b = j₁ := pullback.lift_fst _ _ _
  let J := (openImmersionLowerShriek A j₁).mapDerivedCategoryPlus
  let S := (upperStar A s).mapDerivedCategoryPlus
  let R := (lowerStar A p).rightDerivedFunctorPlus
  let a' := (upperStarLowerStarAdjunction A s).derivedPlus
  have : (lowerStar A s).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction A s)
  let ρ := Functor.rightDerivedFunctorPlusCompIso' (lowerStar A s) (lowerStar A p)
    (lowerStarComp A s p (𝟙 X) sp.symm) ≪≫ lowerStarIdDerivedPlus A X
  let e := (extensionZeroBaseChangeDerivedPlusIso Λ geom.2.2).app K ≪≫
    (openImmersionLowerShriek A s).mapDerivedCategoryPlus.mapIso
      ((upperStarIdDerivedPlus A X).app K)
  let c := (clopenSectionDirectImage_of_commRing Λ p s geom.2.1 sp).choose.app K
  let M := J.obj K
  have hc : c.hom ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A s).unit.app K =
        R.map (a'.unit.app ((openImmersionLowerShriek A s).mapDerivedCategoryPlus.obj K)) ≫
          ρ.hom.app (S.obj ((openImmersionLowerShriek A s).mapDerivedCategoryPlus.obj K)) := by
    have hh := (clopenSectionDirectImage_of_commRing Λ p s geom.2.1 sp).choose_spec K
    have hu := NatTrans.congr_app (exact_unit Λ s) K
    change _ = _ at hu
    rw [hu]
    dsimp only [c, R, a', ρ, S, A, Iso.trans_hom, NatTrans.comp_app, Iso.app_hom]
    simpa only [Category.assoc, rightDerivedLowerStarPlus, Functor.comp_obj] using hh
  have he := restricted_open_unit Λ s b j₁ geom.2.2 K
  have ht := geometric_restriction A s p b f j₁ j₂ sp sb h
    (⟨pullback.condition⟩ : CommSq b p f j₂) M
    ((openImmersionLowerShriek A s).mapDerivedCategoryPlus.obj K) K e c
    ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j₁).unit.app K)
    ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A s).unit.app K) he hc
  unfold properOpenIdentificationOfCommRing
  dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom]
  exact ht

attribute [local irreducible] CategoryTheory.Adjunction.derivedPlus
  upperStarLowerStarAdjunction upperStarCompDerivedPlus

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The finite-coefficient case of `properOpenIdentificationOfCommRing_unit`, kept for its
existing users (`properOpenIdentification` is `properOpenIdentificationOfCommRing` at a finite
ring, `properOpenIdentification_eq_ofCommRing`). -/
theorem properOpenIdentification_unit
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (properOpenIdentification Λ f j₁ j₂ h K).hom ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} Λ) j₁).unit.app K =
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j₁ f j₂ h.symm).hom.app
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)) ≫
        (upperStar (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus.counit.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj
              K)) :=
  properOpenIdentificationOfCommRing_unit Λ f j₁ j₂ h K

end AlgebraicGeometry.Etale
