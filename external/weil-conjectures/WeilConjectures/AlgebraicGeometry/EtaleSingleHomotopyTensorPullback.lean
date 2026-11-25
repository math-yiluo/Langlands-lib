/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory

/-! # Pullback of tensor comparisons for homotopy single complexes -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u uB
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] SymmetricCategory.toBraidedCategory

section Cochain

variable {C D : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C]
  [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]

private lemma singleCochainTensorIso_inv_f (L M : C) :
    (singleCochainTensorIso L M).inv.f 0 =
      HomologicalComplex.ιTensorObj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj L)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M) 0 0 0 rfl := by
  simp [singleCochainTensorIso, CochainComplex.mapBifunctorSingle₁Iso_inv_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    HomologicalComplex.single, whiskerLeft_id]

private lemma singleCochainTensorIso_pullback
    (U : C ⥤ D) [U.Additive] [U.Monoidal] [U.IsLeftAdjoint]
    (L M : C) :
    let T := U.mapHomologicalComplex (.up ℤ)
    let s := HomologicalComplex.single C (.up ℤ) 0
    let s' := HomologicalComplex.single D (.up ℤ) 0
    let c := HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0
    T.map (singleCochainTensorIso L M).hom ≫ c.hom.app (L ⊗ M) ≫
        s'.map (Functor.OplaxMonoidal.δ U L M) =
      Functor.OplaxMonoidal.δ T (s.obj L) (s.obj M) ≫
        (c.hom.app L ⊗ₘ c.hom.app M) ≫
        (singleCochainTensorIso (U.obj L) (U.obj M)).hom := by
  dsimp only
  let T := U.mapHomologicalComplex (.up ℤ)
  let c := HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0
  apply (cancel_epi (c.inv.app (L ⊗ M) ≫ T.map (singleCochainTensorIso L M).inv)).1
  apply (cancel_mono (singleCochainTensorIso (U.obj L) (U.obj M)).inv).1
  dsimp only [T, c]
  simp only [Category.assoc, Iso.inv_hom_id_map_assoc,
    Iso.inv_hom_id_app_assoc, Iso.hom_inv_id, Category.comp_id]
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    singleCochainTensorIso_inv_f]
  rw [Functor.mapCochainComplex_δ]
  simp only [Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
    HomologicalComplex.mapBifunctorComparison_f]
  erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  simp [HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, tensorHom_def,
    CochainComplex.Monoidal.ι_whiskerRight_assoc,
    CochainComplex.ιTensorObj_whiskerLeft_f]

/-- The single/termwise-pullback comparison preserves the tensor comparison after
passing to the homotopy category. No flatness hypothesis is required.
Source: Stacks, Cohomology on Sites, Tags 06YU and 07A4, termwise tensor comparison.
(auxiliary; not a blueprint node).
Proof: precompose the cochain equation with the inverse tensorator and the inverse
single/termwise comparison, and postcompose with the inverse target tensorator.
Morphisms from a single complex are determined in degree zero. The inverse single
tensorator in that degree is the (0,0) tensor inclusion; the defining summand
identity for mapBifunctorComparison gives the ordinary oplax comparison of U.
The single/termwise comparison has identity degree-zero components, so naturality
of the tensor inclusion proves the equation. Apply the homotopy quotient. Its
tensorator is the identity, its functoriality preserves composition and tensor
morphisms, and its induced oplax comparison is the image of the cochain one. -/
theorem singleHomotopyTensorIso_pullback
    (U : C ⥤ D) [U.Additive] [U.Monoidal] [U.IsLeftAdjoint]
    (L M : C) :
    let H := U.mapHomotopyCategory (.up ℤ)
    let q := HomotopyCategory.quotient C (.up ℤ)
    let q' := HomotopyCategory.quotient D (.up ℤ)
    let s := HomologicalComplex.single C (.up ℤ) 0
    let s' := HomologicalComplex.single D (.up ℤ) 0
    let c := HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0
    H.map (q.map (singleCochainTensorIso L M).hom) ≫
        q'.map (c.hom.app (L ⊗ M)) ≫ q'.map (s'.map (Functor.OplaxMonoidal.δ U L M)) =
      Functor.OplaxMonoidal.δ H (q.obj (s.obj L)) (q.obj (s.obj M)) ≫
        (q'.map (c.hom.app L) ⊗ₘ q'.map (c.hom.app M)) ≫
        q'.map (singleCochainTensorIso (U.obj L) (U.obj M)).hom := by
  dsimp only
  have h := (HomotopyCategory.quotient D (.up ℤ)).congr_map
    (singleCochainTensorIso_pullback U L M)
  have hq {K₁ K₂ L₁ L₂ : CochainComplex D ℤ} (f : K₁ ⟶ K₂) (g : L₁ ⟶ L₂) :
      (HomotopyCategory.quotient D (.up ℤ)).map (f ⊗ₘ g) =
        ((HomotopyCategory.quotient D (.up ℤ)).map f ⊗ₘ
          (HomotopyCategory.quotient D (.up ℤ)).map g) := by
    have h := Functor.Monoidal.map_tensor (HomotopyCategory.quotient D (.up ℤ)) f g
    simpa only [show Functor.OplaxMonoidal.δ
        (HomotopyCategory.quotient D (.up ℤ)) K₁ L₁ = 𝟙 _ from rfl,
      show Functor.LaxMonoidal.μ
        (HomotopyCategory.quotient D (.up ℤ)) K₂ L₂ = 𝟙 _ from rfl,
      Category.id_comp, Category.comp_id] using h
  rw [Functor.mapHomotopyCategory_map, Functor.mapHomotopyCategory_δ,
    Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app]
  erw [← hq]
  simpa only [Functor.map_comp, Functor.mapCochainComplex_δ, Category.assoc] using h

end Cochain

end AlgebraicGeometry.Etale
