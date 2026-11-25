/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.BifunctorShift

/-!
# Naturality of the action of a bifunctor on mapping cones

For a bifunctor `F` and a morphism `φ : K₂ ⟶ L₂` of cochain complexes,
`CochainComplex.mapBifunctorMappingCone₂Iso K₁ φ F` identifies `F(K₁, cone φ)` with
`cone (F(K₁, φ))`. This file shows that this isomorphism is natural in `K₁` and in the arrow
`φ`.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace CochainComplex

open HomComplex mappingCone

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [Preadditive C₂] [HasBinaryBiproducts C₂]
  [Preadditive D] [HasBinaryBiproducts D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]

variable {K₁ K₁' : CochainComplex C₁ ℤ} (f₁ : K₁ ⟶ K₁')
  {K₂ L₂ K₂' L₂' : CochainComplex C₂ ℤ} (φ : K₂ ⟶ L₂) (φ' : K₂' ⟶ L₂') (a : K₂ ⟶ K₂')
  (b : L₂ ⟶ L₂') (comm : φ ≫ b = a ≫ φ')

omit [HasBinaryBiproducts C₂] [HasBinaryBiproducts D] in
include comm in
lemma mapBifunctorMap_comm :
    HomologicalComplex.mapBifunctorMap (𝟙 K₁) φ F (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap f₁ b F (.up ℤ) =
      HomologicalComplex.mapBifunctorMap f₁ a F (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 K₁') φ' F (.up ℤ) := by
  ext n p q hpq
  simp only [HomologicalComplex.ι_mapBifunctorMap_assoc, CategoryTheory.Functor.map_id,
    NatTrans.id_app, id_comp, HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f]
  rw [NatTrans.naturality_assoc, ← Functor.map_comp_assoc, ← HomologicalComplex.comp_f, comm,
    HomologicalComplex.comp_f, Functor.map_comp_assoc]

/-- The isomorphism `F(K₁, cone φ) ≅ cone (F(K₁, φ))` is natural in `K₁` and in `φ`. -/
@[reassoc]
lemma mapBifunctorMappingCone₂Iso_inv_naturality :
    mappingCone.map (HomologicalComplex.mapBifunctorMap (𝟙 K₁) φ F (.up ℤ))
      (HomologicalComplex.mapBifunctorMap (𝟙 K₁') φ' F (.up ℤ))
      (HomologicalComplex.mapBifunctorMap f₁ a F (.up ℤ))
      (HomologicalComplex.mapBifunctorMap f₁ b F (.up ℤ))
      (mapBifunctorMap_comm F f₁ φ φ' a b comm) ≫ (mapBifunctorMappingCone₂Iso K₁' φ' F).inv =
      (mapBifunctorMappingCone₂Iso K₁ φ F).inv ≫
        HomologicalComplex.mapBifunctorMap f₁ (mappingCone.map φ φ' a b comm) F (.up ℤ) := by
  apply (Cocycle.equivHom _ _).injective
  ext : 1
  rw [ext_cochain_from_iff _ (-1) 0 (neg_add_cancel 1)]
  constructor
  · ext n m hnm p q hpq
    obtain rfl : m = n - 1 := by omega
    dsimp at hpq
    simp [mappingCone.map, mapBifunctorMappingCone₂Iso.inv,
      Cochain.comp_v _ _ (add_zero (-1)) n (n - 1) (n - 1) (by omega) (by omega),
      mapBifunctorMappingCone₂Iso.ι_ι₁_assoc _ _ _ p q n hpq (n - 1) (by omega) (q - 1)
        (by omega),
      mapBifunctorMappingCone₂Iso.ι_ι₁ _ _ _ p q n hpq (n - 1) (by omega) (q - 1) (by omega),
      NatTrans.naturality_assoc]
    simp only [← Functor.map_comp_assoc, inl_v_desc_f, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v]
  · ext n p q hpq
    simp [mappingCone.map, mapBifunctorMappingCone₂Iso.inv, NatTrans.naturality_assoc]
    simp only [← Functor.map_comp_assoc, inr_f_desc_f, HomologicalComplex.comp_f]

/-- The isomorphism `F(K₁, cone φ) ≅ cone (F(K₁, φ))` is natural in `K₁` and in `φ`. -/
@[reassoc]
lemma mapBifunctorMappingCone₂Iso_hom_naturality :
    HomologicalComplex.mapBifunctorMap f₁ (mappingCone.map φ φ' a b comm) F (.up ℤ) ≫
        (mapBifunctorMappingCone₂Iso K₁' φ' F).hom =
      (mapBifunctorMappingCone₂Iso K₁ φ F).hom ≫
        mappingCone.map (HomologicalComplex.mapBifunctorMap (𝟙 K₁) φ F (.up ℤ))
          (HomologicalComplex.mapBifunctorMap (𝟙 K₁') φ' F (.up ℤ))
          (HomologicalComplex.mapBifunctorMap f₁ a F (.up ℤ))
          (HomologicalComplex.mapBifunctorMap f₁ b F (.up ℤ))
          (mapBifunctorMap_comm F f₁ φ φ' a b comm) := by
  rw [← cancel_epi (mapBifunctorMappingCone₂Iso K₁ φ F).inv, ← cancel_mono
    (mapBifunctorMappingCone₂Iso K₁' φ' F).inv, assoc, assoc, Iso.hom_inv_id, comp_id,
    Iso.inv_hom_id_assoc, mapBifunctorMappingCone₂Iso_inv_naturality]

end CochainComplex
