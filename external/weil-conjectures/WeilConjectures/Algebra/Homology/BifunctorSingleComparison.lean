/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The comparison morphism of a bifunctor on a single complex

Let `F : C₁ ⥤ C₂ ⥤ D` and `F' : C₁' ⥤ C₂' ⥤ D'` be bifunctors, `G₁ : C₁ ⥤ C₁'`,
`G₂ : C₂ ⥤ C₂'` and `G : D ⥤ D'` functors, and
`τ : G (F X₁ X₂) ⟶ F' (G₁ X₁) (G₂ X₂)` a natural transformation. For a cochain complex
`K₁ : CochainComplex C₁ ℤ` and `X₂ : C₂`, we show that the comparison morphism
`HomologicalComplex.mapBifunctorComparison τ (.up ℤ) K₁ ((single C₂ (.up ℤ) 0).obj X₂)`
corresponds, through the identifications `CochainComplex.mapBifunctorSingle₂Iso` of
`mapBifunctor K₁ (single X₂) F` with the complex `F(-, X₂)` applied to `K₁`, to the
degreewise application of `τ(-, X₂)` (`CochainComplex.mapBifunctorComparison_single₂`).
We also show that `CochainComplex.mapBifunctorSingle₂Iso` is natural in `X₂`
(`CochainComplex.mapBifunctorSingle₂Iso_inv_naturality₂`).

-/

@[expose] public section

open CategoryTheory Category Limits HomologicalComplex

namespace CategoryTheory.NatTrans

variable {C₁ C₂ D C₁' C₂' D' : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Category* C₁'] [Category* C₂'] [Category* D']
  {F : C₁ ⥤ C₂ ⥤ D} {F' : C₁' ⥤ C₂' ⥤ D'} {G₁ : C₁ ⥤ C₁'} {G₂ : C₂ ⥤ C₂'} {G : D ⥤ D'}

/-- Given a natural transformation `τ : G (F X₁ X₂) ⟶ F' (G₁ X₁) (G₂ X₂)` and `X₂ : C₂`,
this is the natural transformation `G (F X₁ X₂) ⟶ F' (G₁ X₁) (G₂ X₂)` in `X₁`, with
components `(τ.app X₁).app X₂`. It is `τ.flipApp X₂`, with source and target expressed
as composites of functors. -/
abbrev flipAppComp
    (τ : (Functor.postcompose₂.obj G).obj F ⟶
      (((Functor.whiskeringLeft₂ D').obj G₁).obj G₂).obj F') (X₂ : C₂) :
    F.flip.obj X₂ ⋙ G ⟶ G₁ ⋙ F'.flip.obj (G₂.obj X₂) :=
  τ.flipApp X₂

end CategoryTheory.NatTrans

namespace HomologicalComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

/-- The property `HasMapBifunctor` is invariant under isomorphisms in the second variable. -/
lemma hasMapBifunctor_of_iso₂ (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X₁, (F.obj X₁).PreservesZeroMorphisms] (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]
    (K₁ : HomologicalComplex C₁ c₁) {K₂ K₂' : HomologicalComplex C₂ c₂} (e : K₂ ≅ K₂')
    [HasMapBifunctor K₁ K₂ F c] : HasMapBifunctor K₁ K₂' F c :=
  HomologicalComplex₂.hasTotal_of_iso
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).mapIso e) c

end HomologicalComplex

namespace CochainComplex

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D] [HasZeroObject D]
  [HasZeroObject C₂] (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms] (X₂ : C₂)

/-- The degree `n` component of the inverse of `mapBifunctorSingle₂Iso`: it is the inclusion
of the summand `F (K₁.X n) ((single X₂).X 0)`, precomposed with the identification
`(single X₂).X 0 ≅ X₂`. -/
lemma mapBifunctorSingle₂Iso_inv_f (K₁ : CochainComplex C₁ ℤ) (n : ℤ) :
    (mapBifunctorSingle₂Iso F X₂ K₁).inv.f n =
      (F.obj (K₁.X n)).map (singleObjXSelf (.up ℤ) 0 X₂).inv ≫
        ιMapBifunctor K₁ ((single C₂ (.up ℤ) 0).obj X₂) F (.up ℤ) n 0 n (by simp) := by
  simp [mapBifunctorSingle₂Iso_inv, ComplexShape.σ]

end

variable {C₁ C₂ D C₁' C₂' D' : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Category* C₁'] [Category* C₂'] [Category* D']
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  [HasZeroMorphisms C₁'] [HasZeroMorphisms C₂'] [Preadditive D']
  [HasZeroObject C₂] [HasZeroObject C₂'] [HasZeroObject D] [HasZeroObject D']
  {F : C₁ ⥤ C₂ ⥤ D} [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  {F' : C₁' ⥤ C₂' ⥤ D'} [F'.PreservesZeroMorphisms]
  [∀ X₁, (F'.obj X₁).PreservesZeroMorphisms]
  {G₁ : C₁ ⥤ C₁'} {G₂ : C₂ ⥤ C₂'} {G : D ⥤ D'}
  [G₁.PreservesZeroMorphisms] [G₂.PreservesZeroMorphisms] [G.Additive]
  (τ : (Functor.postcompose₂.obj G).obj F ⟶ (((Functor.whiskeringLeft₂ D').obj G₁).obj G₂).obj F')
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
  (K₁ : CochainComplex C₁ ℤ) (X₂ : C₂)

instance (L₁ : CochainComplex C₁' ℤ) :
    HasMapBifunctor L₁ ((G₂.mapHomologicalComplex (.up ℤ)).obj ((single C₂ (.up ℤ) 0).obj X₂))
      F' (.up ℤ) :=
  hasMapBifunctor_of_iso₂ (K₂ := (single C₂' (.up ℤ) 0).obj (G₂.obj X₂)) F' _ L₁
    ((singleMapHomologicalComplex G₂ (.up ℤ) 0).app X₂).symm

instance (L₁ : CochainComplex C₁' ℤ) :
    HasMapBifunctor L₁ ((single C₂ (.up ℤ) 0 ⋙ G₂.mapHomologicalComplex (.up ℤ)).obj X₂)
      F' (.up ℤ) :=
  inferInstanceAs (HasMapBifunctor L₁
    ((G₂.mapHomologicalComplex (.up ℤ)).obj ((single C₂ (.up ℤ) 0).obj X₂)) F' (.up ℤ))

instance (L₁ : CochainComplex C₁' ℤ) :
    HasMapBifunctor L₁ ((G₂ ⋙ single C₂' (.up ℤ) 0).obj X₂) F' (.up ℤ) :=
  inferInstanceAs (HasMapBifunctor L₁ ((single C₂' (.up ℤ) 0).obj (G₂.obj X₂)) F' (.up ℤ))

omit [G.Additive] in
/-- Degreewise version of `mapBifunctorComparison_single₂`: in degree `n`, the comparison
morphism on `K₁ ⊗ single(X₂)` is `τ` at `(K₁.X n, X₂)`, up to the identifications given by
`mapBifunctorSingle₂Iso`. -/
lemma mapBifunctorComparisonX_single₂ (n : ℤ) :
    G.map ((mapBifunctorSingle₂Iso F X₂ K₁).inv.f n) ≫
      mapBifunctorComparisonX τ (.up ℤ) K₁ ((single C₂ (.up ℤ) 0).obj X₂) n ≫
      (mapBifunctorMap (𝟙 _) ((singleMapHomologicalComplex G₂ (.up ℤ) 0).hom.app X₂) F'
        (.up ℤ)).f n =
    (τ.app (K₁.X n)).app X₂ ≫
      (mapBifunctorSingle₂Iso F' (G₂.obj X₂) ((G₁.mapHomologicalComplex _).obj K₁)).inv.f n := by
  have h := (τ.app (K₁.X n)).naturality (singleObjXSelf (.up ℤ) 0 X₂).inv
  dsimp at h
  rw [mapBifunctorSingle₂Iso_inv_f, mapBifunctorSingle₂Iso_inv_f, Functor.map_comp, assoc,
    map_ιMapBifunctor_mapBifunctorComparisonX_assoc, ι_mapBifunctorMap, reassoc_of% h,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, id_comp,
    singleMapHomologicalComplex_hom_app_self]
  -- the two `F'.obj` below agree only up to unfolding `Functor.mapHomologicalComplex_obj_X`
  erw [← Functor.map_comp_assoc]
  rw [Iso.inv_hom_id_map_assoc]
  rfl

/-- On `K₁ ⊗ single(X₂)`, the comparison morphism `G(K₁ ⊗ X₂) ⟶ G₁(K₁) ⊗ G₂(X₂)` is,
through the identifications `mapBifunctorSingle₂Iso`, the degreewise application of
`τ(-, X₂)`. -/
lemma mapBifunctorComparison_single₂ :
    (G.mapHomologicalComplex _).map (mapBifunctorSingle₂Iso F X₂ K₁).inv ≫
      mapBifunctorComparison τ (.up ℤ) K₁ ((single C₂ (.up ℤ) 0).obj X₂) ≫
      mapBifunctorMap (𝟙 _) ((singleMapHomologicalComplex G₂ (.up ℤ) 0).hom.app X₂) F'
        (.up ℤ) ≫
      (mapBifunctorSingle₂Iso F' (G₂.obj X₂) ((G₁.mapHomologicalComplex _).obj K₁)).hom =
    (NatTrans.mapHomologicalComplex (τ.flipAppComp X₂) (.up ℤ)).app K₁ := by
  rw [← cancel_mono (mapBifunctorSingle₂Iso F' (G₂.obj X₂)
    ((G₁.mapHomologicalComplex _).obj K₁)).inv, assoc, assoc, assoc, Iso.hom_inv_id, comp_id]
  ext n
  exact mapBifunctorComparisonX_single₂ τ K₁ X₂ n

end CochainComplex

namespace CategoryTheory.Functor.OplaxMonoidal

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (G : C ⥤ D) [G.OplaxMonoidal]

/-- For an oplax monoidal functor `G` and `X₂ : C`, the natural transformation
`G (X ⊗ X₂) ⟶ G X ⊗ G X₂` in `X`, with components `δ G X X₂`. -/
@[simps]
def δRightNatTrans (X₂ : C) : tensorRight X₂ ⋙ G ⟶ G ⋙ tensorRight (G.obj X₂) where
  app X := δ G X X₂
  naturality _ _ f := (δ_natural_left G f X₂).symm

end CategoryTheory.Functor.OplaxMonoidal

namespace CochainComplex

open MonoidalCategory Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalPreadditive C] [MonoidalPreadditive D]
  [HasZeroObject C] [HasZeroObject D]
  (G : C ⥤ D) [G.Additive] [G.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
  (K : CochainComplex C ℤ) (X₂ : C)

/-- For an additive oplax monoidal functor `G`, the comparison morphism
`G(K ⊗ X₂) ⟶ G(K) ⊗ G(X₂)` induced by `δ` on the tensor product of a cochain complex `K` with
the single complex `X₂` is, through the identifications `mapBifunctorSingle₂Iso`, the
degreewise morphism `δ G (K.X n) X₂`. (The tensor product `K ⊗ L` of cochain complexes is
definitionally `mapBifunctor K L (curriedTensor C) (.up ℤ)`, although not syntactically.) -/
lemma mapBifunctorComparison_δNatTrans_single₂ :
    (G.mapHomologicalComplex _).map (mapBifunctorSingle₂Iso (curriedTensor C) X₂ K).inv ≫
      mapBifunctorComparison (δNatTrans G) (.up ℤ) K ((single C (.up ℤ) 0).obj X₂) ≫
      mapBifunctorMap (𝟙 _) ((singleMapHomologicalComplex G (.up ℤ) 0).hom.app X₂)
        (curriedTensor D) (.up ℤ) ≫
      (mapBifunctorSingle₂Iso (curriedTensor D) (G.obj X₂)
        ((G.mapHomologicalComplex _).obj K)).hom =
    (NatTrans.mapHomologicalComplex (δRightNatTrans G X₂) (.up ℤ)).app K :=
  mapBifunctorComparison_single₂ (δNatTrans G) K X₂

end CochainComplex

namespace CochainComplex

section Naturality


variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D] [HasZeroObject C₂]
  [HasZeroObject D] (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]

/-- The isomorphism `mapBifunctorSingle₂Iso` is natural in the object placed in degree `0`. -/
@[reassoc]
lemma mapBifunctorSingle₂Iso_inv_naturality₂ {X₂ X₂' : C₂} (f : X₂ ⟶ X₂')
    (K₁ : CochainComplex C₁ ℤ) :
    (NatTrans.mapHomologicalComplex (F.flip.map f) (.up ℤ)).app K₁ ≫
        (mapBifunctorSingle₂Iso F X₂' K₁).inv =
      (mapBifunctorSingle₂Iso F X₂ K₁).inv ≫
        mapBifunctorMap (𝟙 K₁) ((single C₂ (.up ℤ) 0).map f) F (.up ℤ) := by
  ext n
  have h := ι_mapBifunctorMap (𝟙 K₁) ((single C₂ (.up ℤ) 0).map f) F (.up ℤ) n 0 n (by simp)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, mapBifunctorSingle₂Iso_inv_f,
    mapBifunctorSingle₂Iso_inv_f]
  erw [Category.assoc, h]
  rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  calc _ = (F.obj (K₁.X n)).map f ≫ (F.obj (K₁.X n)).map (singleObjXSelf (.up ℤ) 0 X₂').inv ≫
        HomologicalComplex.ιMapBifunctor K₁ ((single C₂ (.up ℤ) 0).obj X₂') F (.up ℤ) n 0 n
          (by simp) := rfl
    _ = (F.obj (K₁.X n)).map (singleObjXSelf (.up ℤ) 0 X₂).inv ≫
        (F.obj (K₁.X n)).map (((single C₂ (.up ℤ) 0).map f).f 0) ≫
        HomologicalComplex.ιMapBifunctor K₁ ((single C₂ (.up ℤ) 0).obj X₂') F (.up ℤ) n 0 n
          (by simp) := by
      rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, single_map_f_self,
        Iso.inv_hom_id_assoc]
    _ = _ := rfl

end Naturality

end CochainComplex

namespace CategoryTheory.Functor.LaxMonoidal

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal]

/-- Moving a morphism `b ≫ F.map c` in the second factor past a morphism `a` in the first factor
and the lax monoidal structure `μ` of `F`. -/
@[reassoc]
lemma whiskerRight_whiskerLeft_μ_map_whiskerLeft {W X : D} {A B B' : C} (a : W ⟶ F.obj A)
    (b : X ⟶ F.obj B) (c : B ⟶ B') :
    a ▷ X ≫ F.obj A ◁ b ≫ μ F A B ≫ F.map (A ◁ c) =
      W ◁ (b ≫ F.map c) ≫ a ▷ F.obj B' ≫ μ F A B' := by
  rw [← μ_natural_right, MonoidalCategory.whiskerLeft_comp_assoc, whisker_exchange_assoc,
    whisker_exchange_assoc]

end CategoryTheory.Functor.LaxMonoidal
