/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-!
# Naturality of `mapBifunctor` with a single complex in the single object

The isomorphisms `CochainComplex.mapBifunctorSingle₁Iso` and
`CochainComplex.mapBifunctorSingle₂Iso`, identifying `F(X[0], K)` with `F(X, -)` applied
termwise to `K` (and symmetrically), are natural in the object `X`.
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

namespace CochainComplex

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D] [HasZeroObject D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma mapBifunctorSingle₁Iso_inv_naturality₁ [HasZeroObject C₁] {X₁ X₁' : C₁} (f : X₁ ⟶ X₁')
    (K₂ : CochainComplex C₂ ℤ) :
    (mapBifunctorSingle₁Iso F X₁ K₂).inv ≫
        mapBifunctorMap ((single C₁ (.up ℤ) 0).map f) (𝟙 K₂) F (.up ℤ) =
      (NatTrans.mapHomologicalComplex (F.map f) (.up ℤ)).app K₂ ≫
        (mapBifunctorSingle₁Iso F X₁' K₂).inv := by
  ext n
  simp [mapBifunctorSingle₁Iso_inv_f, single_map_f_self, ← NatTrans.comp_app_assoc,
    ← Functor.map_comp]

@[reassoc]
lemma mapBifunctorSingle₁Iso_hom_naturality₁ [HasZeroObject C₁] {X₁ X₁' : C₁} (f : X₁ ⟶ X₁')
    (K₂ : CochainComplex C₂ ℤ) :
    mapBifunctorMap ((single C₁ (.up ℤ) 0).map f) (𝟙 K₂) F (.up ℤ) ≫
        (mapBifunctorSingle₁Iso F X₁' K₂).hom =
      (mapBifunctorSingle₁Iso F X₁ K₂).hom ≫
        (NatTrans.mapHomologicalComplex (F.map f) (.up ℤ)).app K₂ := by
  rw [← cancel_epi (mapBifunctorSingle₁Iso F X₁ K₂).inv, Iso.inv_hom_id_assoc,
    mapBifunctorSingle₁Iso_inv_naturality₁_assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc]
lemma mapBifunctorSingle₂Iso_hom_naturality₂ [HasZeroObject C₂] {X₂ X₂' : C₂} (f : X₂ ⟶ X₂')
    (K₁ : CochainComplex C₁ ℤ) :
    mapBifunctorMap (𝟙 K₁) ((single C₂ (.up ℤ) 0).map f) F (.up ℤ) ≫
        (mapBifunctorSingle₂Iso F X₂' K₁).hom =
      (mapBifunctorSingle₂Iso F X₂ K₁).hom ≫
        (NatTrans.mapHomologicalComplex (F.flip.map f) (.up ℤ)).app K₁ := by
  have h := mapBifunctorFlipIso_hom_naturality (F := F) (c := .up ℤ) (𝟙 K₁)
    ((single C₂ (.up ℤ) 0).map f)
  have h' : mapBifunctorMap (𝟙 K₁) ((single C₂ (.up ℤ) 0).map f) F (.up ℤ) ≫
      (mapBifunctorFlipIso K₁ ((single C₂ (.up ℤ) 0).obj X₂') F (.up ℤ)).inv =
      (mapBifunctorFlipIso K₁ ((single C₂ (.up ℤ) 0).obj X₂) F (.up ℤ)).inv ≫
        mapBifunctorMap ((single C₂ (.up ℤ) 0).map f) (𝟙 K₁) F.flip (.up ℤ) := by
    rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]
  simp only [mapBifunctorSingle₂Iso_hom, Category.assoc]
  rw [reassoc_of% h', mapBifunctorSingle₁Iso_hom_naturality₁]

end CochainComplex
