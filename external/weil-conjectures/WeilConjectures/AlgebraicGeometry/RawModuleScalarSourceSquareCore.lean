/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Generic derived source-square calculation used by the scalar source square.
(blueprint: lem-sbc-raw-scalar-source-square).

The theorem is the generic part of the single-complex argument: it packages
the compatibility of the three derived composition comparisons with arbitrary
source maps. The concrete scalar theorem supplies the source equation and
instantiates this statement.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor
namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
  [Abelian C] [Abelian D] [Abelian E] [Abelian B]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasDerivedCategory B]

set_option linter.flexible false in
private lemma single_hom (G : C ⥤ D) [G.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G] (n : ℤ) (X : C) :
    (G.mapDerivedCategorySingleFunctor n).hom.app X =
      G.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single C (.up ℤ) n).obj X) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) n).hom.app X) := by
  simp [mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
  erw [Category.id_comp]

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] in
private lemma complex_single_comp (G : C ⥤ D) (H : D ⥤ E) [G.Additive] [H.Additive]
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

private lemma derived_single_comp (G : C ⥤ D) (H : D ⥤ E) [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H] (n : ℤ) (X : C) :
    (mapDerivedCategoryCompIso G H).inv.app ((DerivedCategory.singleFunctor C n).obj X) ≫
      H.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor n).hom.app X) ≫
      (H.mapDerivedCategorySingleFunctor n).hom.app (G.obj X) =
    ((G ⋙ H).mapDerivedCategorySingleFunctor n).hom.app X := by
  rw [single_hom G, single_hom H, single_hom (G ⋙ H), Functor.map_comp]
  simp only [Category.assoc]
  erw [mapDerivedCategoryFactors_hom_naturality_assoc]
  have hf := mapDerivedCategoryCompIso_fac G H
    ((HomologicalComplex.single C (.up ℤ) n).obj X)
  have hc : (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) (.up ℤ)).hom.app
      ((HomologicalComplex.single C (.up ℤ) n).obj X) = 𝟙 _ := rfl
  rw [hc] at hf
  erw [Functor.map_id, Category.comp_id] at hf
  erw [← DerivedCategory.Q.map_comp, complex_single_comp]
  erw [reassoc_of% hf]

omit [HasDerivedCategory C] [HasDerivedCategory D] in
private lemma complex_single_natIso {G H : C ⥤ D} [G.Additive] [H.Additive]
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

private lemma derived_single_natIso {G H : C ⥤ D} [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (e : G ≅ H) (n : ℤ) (X : C) :
    (mapDerivedCategoryNatIso e).hom.app ((DerivedCategory.singleFunctor C n).obj X) ≫
      (H.mapDerivedCategorySingleFunctor n).hom.app X =
    (G.mapDerivedCategorySingleFunctor n).hom.app X ≫
      (DerivedCategory.singleFunctor D n).map (e.hom.app X) := by
  rw [single_hom H, single_hom G]
  simp only [Category.assoc]
  erw [mapDerivedCategoryNatIso_fac_assoc, ← DerivedCategory.Q.map_comp,
    complex_single_natIso, DerivedCategory.Q.map_comp]
  rfl

private lemma plus_single_comp (G : C ⥤ D) (H : D ⥤ E) [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H] (n : ℤ) (X : C) :
    (mapDerivedCategoryPlusCompIso G H).hom.app
        ((DerivedCategory.Plus.singleFunctor C n).obj X) ≫
      H.mapDerivedCategoryPlus.map ((G.mapDerivedCategoryPlusSingleFunctor n).hom.app X) ≫
      (H.mapDerivedCategoryPlusSingleFunctor n).hom.app (G.obj X) =
    ((G ⋙ H).mapDerivedCategoryPlusSingleFunctor n).hom.app X := by
  apply DerivedCategory.Plus.ι.map_injective
  have hmap : ∀ {X Y : DerivedCategory.Plus D} (f : X ⟶ Y),
      DerivedCategory.Plus.ι.map (H.mapDerivedCategoryPlus.map f) =
        H.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := fun _ => rfl
  simp only [Functor.map_comp, hmap, ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app]
  exact derived_single_comp G H n X

private lemma plus_single_natIso {G H : C ⥤ D} [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (e : G ≅ H) (n : ℤ) (X : C) :
    (mapDerivedCategoryPlusNatIso e).hom.app
        ((DerivedCategory.Plus.singleFunctor C n).obj X) ≫
      (H.mapDerivedCategoryPlusSingleFunctor n).hom.app X =
    (G.mapDerivedCategoryPlusSingleFunctor n).hom.app X ≫
      (DerivedCategory.Plus.singleFunctor D n).map (e.hom.app X) := by
  apply DerivedCategory.Plus.ι.map_injective
  have hsingle : ∀ {X Y : D} (f : X ⟶ Y),
      DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.singleFunctor D n).map f) =
        (DerivedCategory.singleFunctor D n).map f := fun _ => rfl
  simp only [Functor.map_comp, hsingle, ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app]
  exact derived_single_natIso e n X


/-- Generic single-complex source-square calculation.
Source: Mathlib DerivedCategory.ExactFunctor factorization equations and the
private single-complex calculations of EtalePullbackSingleComp.
Proof: the single-complex composition and natural-isomorphism equations hold
in degree n by the canonical identity comparison, and in other degrees by
zero-object uniqueness. Localization Q, its factorization naturality, and
full faithfulness of the bounded-below inclusion give the two derived equations.
Combine these equations for the composite d. Postcompose the desired square
with d.hom and then H of the V-single hom followed by the H-single hom.
These are isomorphisms. Naturality moves m and cB across the single comparisons;
functoriality and inverse-hom cancellation reduce the goal to hs postcomposed
with e.hom. Cancel e.inv followed by e.hom.
(blueprint: lem-sbc-raw-scalar-source-square-core). -/
theorem plus_single_source_square_core
    (M : C ⥤ D) (V' : D ⥤ B) (V : C ⥤ E) (H : E ⥤ B)
    [M.Additive] [V'.Additive] [V.Additive] [H.Additive]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [PreservesFiniteLimits V'] [PreservesFiniteColimits V']
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : M ⋙ V' ≅ V ⋙ H) (n : ℤ)
    {LA : D} {LB : C} {EA : B} {EB : E}
    (m : LA ⟶ M.obj LB) (k : EA ⟶ H.obj EB)
    (cA : EA ⟶ V'.obj LA) (cB : EB ⟶ V.obj LB)
    (hs : cA ≫ V'.map m = k ≫ H.map cB ≫ e.inv.app LB) :
    ((DerivedCategory.Plus.singleFunctor B n).map cA ≫
        (V'.mapDerivedCategoryPlusSingleFunctor n).inv.app LA) ≫
        V'.mapDerivedCategoryPlus.map
          ((DerivedCategory.Plus.singleFunctor D n).map m ≫
            (M.mapDerivedCategoryPlusSingleFunctor n).inv.app LB) =
      ((DerivedCategory.Plus.singleFunctor B n).map k ≫
          (H.mapDerivedCategoryPlusSingleFunctor n).inv.app EB) ≫
        H.mapDerivedCategoryPlus.map
          ((DerivedCategory.Plus.singleFunctor E n).map cB ≫
            (V.mapDerivedCategoryPlusSingleFunctor n).inv.app LB) ≫
        ((mapDerivedCategoryPlusCompIso M V').symm ≪≫
          mapDerivedCategoryPlusNatIso e ≪≫ mapDerivedCategoryPlusCompIso V H).inv.app
            ((DerivedCategory.Plus.singleFunctor C n).obj LB) := by
  let d := (mapDerivedCategoryPlusCompIso M V').symm ≪≫
    mapDerivedCategoryPlusNatIso e ≪≫ mapDerivedCategoryPlusCompIso V H
  have hd : d.hom.app ((DerivedCategory.Plus.singleFunctor C n).obj LB) ≫
      H.mapDerivedCategoryPlus.map ((V.mapDerivedCategoryPlusSingleFunctor n).hom.app LB) ≫
      (H.mapDerivedCategoryPlusSingleFunctor n).hom.app (V.obj LB) =
    V'.mapDerivedCategoryPlus.map ((M.mapDerivedCategoryPlusSingleFunctor n).hom.app LB) ≫
      (V'.mapDerivedCategoryPlusSingleFunctor n).hom.app (M.obj LB) ≫
      (DerivedCategory.Plus.singleFunctor B n).map (e.hom.app LB) := by
    dsimp [d]
    simp only [Category.assoc]
    rw [plus_single_comp V H n LB,
      plus_single_natIso e n LB]
    rw [← plus_single_comp M V' n LB]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← cancel_mono (d.hom.app ((DerivedCategory.Plus.singleFunctor C n).obj LB))]
  dsimp only [d]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← cancel_mono
    (H.mapDerivedCategoryPlus.map ((V.mapDerivedCategoryPlusSingleFunctor n).hom.app LB) ≫
      (H.mapDerivedCategoryPlusSingleFunctor n).hom.app (V.obj LB))]
  simp only [Category.assoc]
  rw [hd]
  simp only [Functor.map_comp, Category.assoc]
  erw [Category.id_comp]
  rw [← V'.mapDerivedCategoryPlus.map_comp_assoc
    ((M.mapDerivedCategoryPlusSingleFunctor n).inv.app LB)
    ((M.mapDerivedCategoryPlusSingleFunctor n).hom.app LB)]
  rw [← H.mapDerivedCategoryPlus.map_comp_assoc
    ((V.mapDerivedCategoryPlusSingleFunctor n).inv.app LB)
    ((V.mapDerivedCategoryPlusSingleFunctor n).hom.app LB)]
  simp only [Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  rw [reassoc_of% ((V'.mapDerivedCategoryPlusSingleFunctor n).inv.naturality m).symm]
  rw [reassoc_of% ((H.mapDerivedCategoryPlusSingleFunctor n).inv.naturality cB).symm]
  simp only [Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
  erw [Category.comp_id]
  rw [← Functor.map_comp]
  apply (DerivedCategory.Plus.singleFunctor B n).congr_map
  rw [reassoc_of% hs]
  simp only [Iso.inv_hom_id_app]
  erw [Category.comp_id]

end CategoryTheory.Functor
