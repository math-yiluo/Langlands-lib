/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageMap
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-! # Canonical-coefficient composition for abelian higher direct images

Source: Stacks Project, Tag 09Z1, canonical comparison maps.
(blueprint: lem-sbc-abelian-higher-direct-image-core-comp).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Reassociate a mapped comparison without unfolding the concrete derived functors. -/
private lemma assemble_mapped_comparison {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (H : D ⥤ E) {V : D} {X₀ X₁ X₂ X₃ X₄ : C}
    (u : V ⟶ R.obj X₀) (c : X₀ ⟶ X₁) (d : X₁ ⟶ X₂)
    (s : X₂ ⟶ X₃) (f : X₃ ⟶ X₄) :
    H.map (u ≫ R.map (c ≫ d ≫ s ≫ f)) =
      H.map ((u ≫ R.map (c ≫ d)) ≫ R.map (s ≫ f)) := by
  simp only [Functor.map_comp, Category.assoc]

private lemma single_hom {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (G : C ⥤ D) [G.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G] (n : ℤ) (X : C) :
    (G.mapDerivedCategorySingleFunctor n).hom.app X =
      G.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single C (.up ℤ) n).obj X) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) n).hom.app X) := by
  simp only [Functor.comp_obj, CategoryTheory.Functor.mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ, Functor.isoWhiskerRight_refl,
    Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, DerivedCategory.Q_obj_single_obj,
    Functor.whiskerRight_app, NatTrans.id_app, Category.comp_id, Category.id_comp]
  erw [Category.id_comp]

private lemma complex_single_comp {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E] (G : C ⥤ D) (H : D ⥤ E) [G.Additive] [H.Additive]
    (n : ℤ) (X : C) :
    (H.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) n).hom.app X) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) n).hom.app (G.obj X) =
    (HomologicalComplex.singleMapHomologicalComplex (G ⋙ H) (.up ℤ) n).hom.app X := by
  ext i
  by_cases hi : i = n
  · subst i
    simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne, hi]

private lemma derived_single_comp {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (G : C ⥤ D) (H : D ⥤ E) [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H] (n : ℤ) (X : C) :
    (CategoryTheory.Functor.mapDerivedCategoryCompIso G H).inv.app
        ((DerivedCategory.singleFunctor C n).obj X) ≫
      H.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor n).hom.app X) ≫
      (H.mapDerivedCategorySingleFunctor n).hom.app (G.obj X) =
    ((G ⋙ H).mapDerivedCategorySingleFunctor n).hom.app X := by
  rw [single_hom G, single_hom H, single_hom (G ⋙ H), Functor.map_comp]
  simp only [Category.assoc]
  erw [CategoryTheory.Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
  have hf := CategoryTheory.Functor.mapDerivedCategoryCompIso_fac G H
    ((HomologicalComplex.single C (.up ℤ) n).obj X)
  have hc : (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) (.up ℤ)).hom.app
      ((HomologicalComplex.single C (.up ℤ) n).obj X) = 𝟙 _ := rfl
  rw [hc] at hf
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hf
  erw [← DerivedCategory.Q.map_comp, complex_single_comp]
  erw [reassoc_of% hf]

private lemma complex_single_natIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] {G H : C ⥤ D} [G.Additive] [H.Additive]
    (e : G ≅ H) (n : ℤ) (X : C) :
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((HomologicalComplex.single C (.up ℤ) n).obj X) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) n).hom.app X =
    (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) n).hom.app X ≫
      (HomologicalComplex.single D (.up ℤ) n).map (e.hom.app X) := by
  ext i
  by_cases hi : i = n
  · subst i
    simp only [HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      HomologicalComplex.single_map_f_self]
  · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne, hi]

private lemma derived_single_natIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] {G H : C ⥤ D} [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (e : G ≅ H) (n : ℤ) (X : C) :
    (CategoryTheory.Functor.mapDerivedCategoryNatIso e).hom.app
        ((DerivedCategory.singleFunctor C n).obj X) ≫
      (H.mapDerivedCategorySingleFunctor n).hom.app X =
    (G.mapDerivedCategorySingleFunctor n).hom.app X ≫
      (DerivedCategory.singleFunctor D n).map (e.hom.app X) := by
  rw [single_hom H, single_hom G]
  simp only [Category.assoc]
  erw [CategoryTheory.Functor.mapDerivedCategoryNatIso_fac_assoc, ← DerivedCategory.Q.map_comp,
    complex_single_natIso, DerivedCategory.Q.map_comp]
  rfl

private lemma plus_single_comp {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (G : C ⥤ D) (H : D ⥤ E) [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H] (n : ℤ) (X : C) :
    (CategoryTheory.Functor.mapDerivedCategoryPlusCompIso G H).hom.app
        ((DerivedCategory.Plus.singleFunctor C n).obj X) ≫
      H.mapDerivedCategoryPlus.map ((G.mapDerivedCategoryPlusSingleFunctor n).hom.app X) ≫
      (H.mapDerivedCategoryPlusSingleFunctor n).hom.app (G.obj X) =
    ((G ⋙ H).mapDerivedCategoryPlusSingleFunctor n).hom.app X := by
  apply DerivedCategory.Plus.ι.map_injective
  have hmap : ∀ {X Y : DerivedCategory.Plus D} (f : X ⟶ Y),
      DerivedCategory.Plus.ι.map (H.mapDerivedCategoryPlus.map f) =
        H.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := fun _ => rfl
  simp only [Functor.map_comp, hmap,
    CategoryTheory.Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    CategoryTheory.Functor.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app]
  exact derived_single_comp G H n X

private lemma plus_single_natIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] {G H : C ⥤ D} [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (e : G ≅ H) (n : ℤ) (X : C) :
    (CategoryTheory.Functor.mapDerivedCategoryPlusNatIso e).hom.app
        ((DerivedCategory.Plus.singleFunctor C n).obj X) ≫
      (H.mapDerivedCategoryPlusSingleFunctor n).hom.app X =
    (G.mapDerivedCategoryPlusSingleFunctor n).hom.app X ≫
      (DerivedCategory.Plus.singleFunctor D n).map (e.hom.app X) := by
  apply DerivedCategory.Plus.ι.map_injective
  have hsingle : ∀ {X Y : D} (f : X ⟶ Y),
      DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.singleFunctor D n).map f) =
        (DerivedCategory.singleFunctor D n).map f := fun _ => rfl
  simp only [Functor.map_comp, hsingle,
    CategoryTheory.Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    CategoryTheory.Functor.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app]
  exact derived_single_natIso e n X


/-- The single-complex comparisons commute with the derived pullback composition.
Source: Stacks Tags 0D6D and 09Z1. Proof: the degreewise single-complex equality,
transported through the derived localization and its fully faithful plus inclusion. -/
private theorem abelianUpperStarPlusComp_single
    {T T₁ T₂ : Scheme.{v}} (b : T₁ ⟶ T₂) (a : T₂ ⟶ T)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (upperStarPlusComp AddCommGrpCat.{v + 1} b a).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      D+((b)^*[AddCommGrpCat.{v + 1}]).map
        ((((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
      ((((b)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((a)^*[AddCommGrpCat.{v + 1}]).obj F)) =
    ((((b ≫ a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp AddCommGrpCat.{v + 1} b a).hom.app F) := by
  rw [upperStarPlusComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [plus_single_comp
    (a)^*[AddCommGrpCat.{v + 1}] (b)^*[AddCommGrpCat.{v + 1}] 0 F,
    plus_single_natIso (upperStarComp AddCommGrpCat.{v + 1} b a) 0 F]

/-- The derived comparison before inserting the single-complex identification.
Source: Stacks Tag 09Z1; the adjunct of pullback of the counit. -/
private noncomputable def abelianDerivedTransition {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})) :
    R+((h)_*[AddCommGrpCat.{v + 1}]).obj K ⟶
      R+((h')_*[AddCommGrpCat.{v + 1}]).obj
        (D+((a)^*[AddCommGrpCat.{v + 1}]).obj K) :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h').derivedPlus.unit.app _ ≫
    R+((h')_*[AddCommGrpCat.{v + 1}]).map
      (((eqToIso (congrArg
          (fun t : Y' ⟶ S ↦ ((t)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlus)
          w.symm)).hom.app _ ≫
        (upperStarPlusComp AddCommGrpCat.{v + 1} a h).hom.app _) ≫
        D+((a)^*[AddCommGrpCat.{v + 1}]).map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h).derivedPlus.counit.app K))

/-- Naturality of the derived comparison in its complex, by naturality of the
unit, composition comparison and counit. Source: Stacks Tag 09Z1. -/
private lemma abelianDerivedTransition_naturality {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    {K L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})}
    (f : K ⟶ L) :
    R+((h)_*[AddCommGrpCat.{v + 1}]).map f ≫ abelianDerivedTransition a h h' w L =
      abelianDerivedTransition a h h' w K ≫
        R+((h')_*[AddCommGrpCat.{v + 1}]).map
          (D+((a)^*[AddCommGrpCat.{v + 1}]).map f) := by
  subst h'
  let A := AddCommGrpCat.{v + 1}
  let adj := (upperStarLowerStarAdjunction A (a ≫ h)).derivedPlus
  let c := upperStarPlusComp A a h
  have ht (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)) :
      abelianDerivedTransition a h (a ≫ h) rfl M =
        (adj.homEquiv _ _) (c.hom.app (R+((h)_*[A]).obj M) ≫
          D+((a)^*[A]).map
            ((upperStarLowerStarAdjunction A h).derivedPlus.counit.app M)) := by
    simp only [abelianDerivedTransition, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp]
    rfl
  rw [ht, ht]
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm]
  dsimp only [A, Functor.id_obj]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hn := c.hom.naturality (R+((h)_*[A]).map f)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  have hn' := (upperStarLowerStarAdjunction A h).derivedPlus.counit.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hn'
  rw [hn', Functor.map_comp, Category.assoc]

private theorem abelianDerivedTransition_comp
    {X Y Y₁ Y₂ : Scheme.{v}} (h : Y ⟶ X)
    (a₂ : Y₂ ⟶ Y) (h₂ : Y₂ ⟶ X) (wh₂ : a₂ ≫ h = h₂)
    (a₁ : Y₁ ⟶ Y₂) (h₁ : Y₁ ⟶ X) (wh₁ : a₁ ≫ h₂ = h₁)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (AddCommGrpCat.{v + 1}))) :
    abelianDerivedTransition a₂ h h₂ wh₂ K ≫
        abelianDerivedTransition a₁ h₂ h₁ wh₁
          (D+((a₂)^*[AddCommGrpCat.{v + 1}]).obj K) ≫
        R+((h₁)_*[AddCommGrpCat.{v + 1}]).map
          ((Etale.upperStarPlusComp (AddCommGrpCat.{v + 1}) a₁ a₂).inv.app K) =
      abelianDerivedTransition (a₁ ≫ a₂) h h₁
        (by rw [Category.assoc, wh₂, wh₁]) K := by
  subst h₂
  subst h₁
  let A := AddCommGrpCat.{v + 1}
  let adj₀ := (Etale.upperStarLowerStarAdjunction A h).derivedPlus
  let adj₂ := (Etale.upperStarLowerStarAdjunction A (a₂ ≫ h)).derivedPlus
  let adj₁ := (Etale.upperStarLowerStarAdjunction A (a₁ ≫ a₂ ≫ h)).derivedPlus
  let c₂ := Etale.upperStarPlusComp A a₂ h
  let c₁ := Iso.refl D+((a₁ ≫ a₂ ≫ h)^*[A]) ≪≫
    Etale.upperStarPlusComp A a₁ (a₂ ≫ h)
  let t₂ := abelianDerivedTransition a₂ h (a₂ ≫ h) rfl K
  let f₂ := c₂.hom.app (R+((h)_*[A]).obj K) ≫
    D+((a₂)^*[A]).map (adj₀.counit.app K)
  have ht₂ : (adj₂.homEquiv (R+((h)_*[A]).obj K)
      (D+((a₂)^*[A]).obj K)).symm t₂ = f₂ := by
    have he : t₂ = (adj₂.homEquiv (R+((h)_*[A]).obj K)
        (D+((a₂)^*[A]).obj K)) f₂ := by
      simp only [t₂, abelianDerivedTransition, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
        Category.id_comp]
      rfl
    rw [he]
    exact Equiv.symm_apply_apply _ f₂
  let c := eqToIso (show D+((a₁ ≫ a₂ ≫ h)^*[A]) =
      D+(((a₁ ≫ a₂) ≫ h)^*[A]) by rw [Category.assoc]) ≪≫
    Etale.upperStarPlusComp A (a₁ ≫ a₂) h
  change D+((a₂ ≫ h)^*[A]).map t₂ ≫ adj₂.counit.app _ = f₂ at ht₂
  apply (adj₁.homEquiv _ _).symm.injective
  rw [← Category.assoc t₂, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm]
  change (D+((a₁ ≫ a₂ ≫ h)^*[A]).map t₂ ≫
      (adj₁.homEquiv _ _).symm ((adj₁.homEquiv _ _)
        (c₁.hom.app _ ≫ D+((a₁)^*[A]).map (adj₂.counit.app _)))) ≫
      (Etale.upperStarPlusComp A a₁ a₂).inv.app K =
    (adj₁.homEquiv _ _).symm ((adj₁.homEquiv _ _)
      (c.hom.app _ ≫ D+((a₁ ≫ a₂)^*[A]).map (adj₀.counit.app K)))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hn := c₁.hom.naturality t₂
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc (D+((a₁ ≫ a₂ ≫ h)^*[A]).map t₂), hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ht₂]
  dsimp only [f₂]
  rw [Functor.map_comp]
  have ha := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc A a₁ a₂ h
    (a₁ ≫ a₂) (a₂ ≫ h) (a₁ ≫ a₂ ≫ h) rfl rfl (Category.assoc _ _ _).symm)
    (R+((h)_*[A]).obj K)
  simp only [Etale.upperStarCompDerivedPlus_eq_eqToIso_trans, eqToIso_refl,
    Iso.refl_trans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at ha
  have ha' : c₁.hom.app (R+((h)_*[A]).obj K) ≫
      D+((a₁)^*[A]).map (c₂.hom.app _) =
      c.hom.app _ ≫ (Etale.upperStarPlusComp A a₁ a₂).hom.app _ := by
    simpa only [c₁, c₂, c, eqToIso_refl, Iso.refl_trans] using ha
  simp only [Category.assoc]
  rw [← Category.assoc (c₁.hom.app _), ha']
  have hn' := (Etale.upperStarPlusComp A a₁ a₂).inv.naturality (adj₀.counit.app K)
  dsimp only [Functor.comp_map] at hn'
  change D+((a₁)^*[A]).map (D+((a₂)^*[A]).map (adj₀.counit.app K)) ≫
      (Etale.upperStarPlusComp A a₁ a₂).inv.app K =
      (Etale.upperStarPlusComp A a₁ a₂).inv.app
        (D+((h)^*[A]).obj (R+((h)_*[A]).obj K)) ≫
      D+((a₁ ≫ a₂)^*[A]).map (adj₀.counit.app K) at hn'
  simp only [Category.assoc]
  rw [hn']
  simp only [← Category.assoc, Iso.hom_inv_id_app]
  change (c.hom.app (R+((h)_*[A]).obj K) ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]


/-- Expand the comparison as a derived transition followed by the coefficient map.
Source: Stacks Tag 09Z1; associativity and functoriality of direct image. -/
private lemma abelianHigherDirectImageMap_eq {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F') :
    abelianHigherDirectImageMap a h h' w p F F' φ =
      (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).map
        (abelianDerivedTransition a h h' w ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
          R+((h')_*[AddCommGrpCat.{v + 1}]).map
            ((((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
              (DerivedCategory.Plus.singleFunctor _ 0).map φ)) := by
  subst h'
  simp only [abelianHigherDirectImageMap, abelianDerivedTransition, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let M := R+((h)_*[AddCommGrpCat.{v + 1}]).obj K
  exact assemble_mapped_comparison
    R+((a ≫ h)_*[AddCommGrpCat.{v + 1}])
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) (p : ℤ))
    ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} (a ≫ h)).derivedPlus.unit.app M)
    ((upperStarPlusComp AddCommGrpCat.{v + 1} a h).hom.app M)
    (D+((a)^*[AddCommGrpCat.{v + 1}]).map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h).derivedPlus.counit.app K))
    ((((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
    ((DerivedCategory.Plus.singleFunctor _ 0).map φ)

/-- Composition with canonical pullback coefficients, before inserting arbitrary
coefficient morphisms. Source: Stacks Project, Tag 09Z1, canonical comparison maps.
(blueprint: lem-sbc-abelian-higher-direct-image-core-comp).

Proof: Expand the two maps as the derived adjunction units followed by direct
images of pullback comparisons and counits, and the single-complex comparisons.
Transpose along the h'' derived adjunction. Naturality moves the intermediate
unit past the first pulled-back counit. The h' triangle identity cancels the
intermediate counit and unit. Associativity of the inverse-image comparison
identifies the remaining counit composite with that for b followed by a.
The composition comparison for exact functors commutes with single complexes:
on their degree-zero representatives this is the ordinary pullback composition
comparison, and localization preserves this equality. Apply degree-p homology,
which preserves composition. The proofs of the structure-map equalities agree
by proof irrelevance. This works for identity scheme maps, zero sheaves, and
p = 0, with no geometric hypotheses. -/
theorem abelianHigherDirectImage_core_comp {S Y Y' Y'' : Scheme.{v}}
    (a : Y' ⟶ Y) (b : Y'' ⟶ Y') (h : Y ⟶ S) (h' : Y' ⟶ S) (h'' : Y'' ⟶ S)
    (wa : a ≫ h = h') (wb : b ≫ h' = h'') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    abelianHigherDirectImageMap (b ≫ a) h h''
        (by rw [Category.assoc, wa, wb]) p F
        (((b)^*[AddCommGrpCat.{v + 1}]).obj
          (((a)^*[AddCommGrpCat.{v + 1}]).obj F))
        ((upperStarComp AddCommGrpCat.{v + 1} b a).hom.app F) =
      abelianHigherDirectImageMap a h h' wa p F
          (((a)^*[AddCommGrpCat.{v + 1}]).obj F) (𝟙 _) ≫
        abelianHigherDirectImageMap b h' h'' wb p
          (((a)^*[AddCommGrpCat.{v + 1}]).obj F)
          (((b)^*[AddCommGrpCat.{v + 1}]).obj
            (((a)^*[AddCommGrpCat.{v + 1}]).obj F)) (𝟙 _) := by
  rw [abelianHigherDirectImageMap_eq, abelianHigherDirectImageMap_eq,
    abelianHigherDirectImageMap_eq]
  simp only [CategoryTheory.Functor.map_id]
  erw [CategoryTheory.Category.comp_id, CategoryTheory.Category.comp_id]
  rw [← Functor.map_comp]
  congr 1
  let A := AddCommGrpCat.{v + 1}
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let sₐ := (((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F
  let sᵦ := (((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app (((a)^*[A]).obj F)
  let sᵦₐ := (((b ≫ a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F
  let c := upperStarPlusComp A b a
  let R := R+((h'')_*[A])
  let tₐ := abelianDerivedTransition a h h' wa K
  let tᵦ := abelianDerivedTransition b h' h'' wb (D+((a)^*[A]).obj K)
  let tᵦₐ := abelianDerivedTransition (b ≫ a) h h''
    (by rw [Category.assoc, wa, wb]) K
  have hn := abelianDerivedTransition_naturality b h' h'' wb sₐ
  have hc := abelianDerivedTransition_comp h a h' wa b h'' wb K
  have hs := abelianUpperStarPlusComp_single b a F
  change tᵦₐ ≫ R.map (sᵦₐ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp A b a).hom.app F)) =
    (tₐ ≫ R+((h')_*[A]).map sₐ) ≫
      (abelianDerivedTransition b h' h'' wb
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((a)^*[A]).obj F)) ≫ R.map sᵦ)
  change tₐ ≫ tᵦ ≫ R.map (c.inv.app K) = tᵦₐ at hc
  change c.hom.app K ≫ D+((b)^*[A]).map sₐ ≫ sᵦ =
    sᵦₐ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp A b a).hom.app F) at hs
  rw [← hs, ← hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.assoc (R+((h')_*[A]).map sₐ)]
  erw [hn]
  simp only [Category.assoc]
  rfl

end AlgebraicGeometry.Etale
