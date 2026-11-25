/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-!
# The tensor comparison of the derived functor of an exact monoidal functor

Let `F : C ⥤ D` be an exact strong monoidal functor between monoidal Grothendieck abelian
categories with functorial flat resolutions, which preserves flat objects and is a left adjoint.
The tensor comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M`
(`CategoryTheory.Functor.leftDerivedTensorComparison`), transported along the identification
`LF ≅ D(F)` of the left derived functor with the levelwise functor, gives a comparison
`D(F)(K ⊗ᴸ M) ⟶ D(F) K ⊗ᴸ D(F) M` (`CategoryTheory.Functor.mapDerivedCategoryTensorComparison`).

## Main definitions and results

- `CategoryTheory.Functor.mapDerivedCategoryTensorComparison_app_app_comp`: on objects of the
  homotopy category, the comparison is induced by the comonoidal structure of `F`.
- `CategoryTheory.Functor.mapDerivedCategoryOplaxMonoidal`: `D(F)` is oplax monoidal with this
  comparison, and its unit comparison is an isomorphism
  (`CategoryTheory.Functor.isIso_mapDerivedCategoryOplaxMonoidal_η`).
- `CategoryTheory.Functor.commShift_mapDerivedCategoryTensorComparison_app`: for a fixed `K`, the
  comparison `D(F)(K ⊗ᴸ -) ⟶ D(F) K ⊗ᴸ D(F)(-)` commutes with the shifts.
-/

@[expose] public section

universe u u₁ u₂

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

section TensorHom

variable {E : Type*} [Category* E] {D : Type*} [Category* D] [MonoidalCategory D]
  {G G' : E ⥤ D}

/-- For a natural transformation `α : G ⟶ G'`, the morphism of bifunctors
`G X ⊗ G Y ⟶ G' X ⊗ G' Y` with components `α X ⊗ₘ α Y`. -/
def tensorHomNatTrans (α : G ⟶ G') :
    (((whiskeringLeft₂ D).obj G).obj G).obj (curriedTensor D) ⟶
      (((whiskeringLeft₂ D).obj G').obj G').obj (curriedTensor D) where
  app X :=
    { app Y := α.app X ⊗ₘ α.app Y
      naturality Y Y' f := by
        dsimp
        rw [whiskerLeft_comp_tensorHom, tensorHom_comp_whiskerLeft, α.naturality] }
  naturality X X' f := by
    refine NatTrans.ext (funext fun Y ↦ ?_)
    dsimp
    rw [whiskerRight_comp_tensorHom, tensorHom_comp_whiskerRight, α.naturality]

@[simp]
lemma tensorHomNatTrans_app_app (α : G ⟶ G') (X Y : E) :
    ((tensorHomNatTrans α).app X).app Y = α.app X ⊗ₘ α.app Y :=
  rfl

end TensorHom

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

local instance hasColimitsOfSize_mapDerivedCategoryMonoidal₁ : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

local instance hasColimitsOfSize_mapDerivedCategoryMonoidal₂ : HasColimitsOfSize.{0, 0} D :=
  hasColimitsOfSizeShrink D

/-- The tensor comparison `D(F)(K ⊗ᴸ M) ⟶ D(F) K ⊗ᴸ D(F) M` of the functor induced by `F` on
derived categories: the tensor comparison of the left derived functor `LF`
(`CategoryTheory.Functor.leftDerivedTensorComparison`), transported along
`LF ≅ D(F)` (`CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory`). -/
noncomputable def mapDerivedCategoryTensorComparison :
    (postcompose₂.obj F.mapDerivedCategory).obj (curriedTensor _) ⟶
      (((whiskeringLeft₂ _).obj F.mapDerivedCategory).obj F.mapDerivedCategory).obj
        (curriedTensor _) :=
  (postcompose₂.map F.leftDerivedFunctorIsoMapDerivedCategory.inv).app _ ≫
    F.leftDerivedTensorComparison ≫ tensorHomNatTrans F.leftDerivedFunctorIsoMapDerivedCategory.hom

lemma mapDerivedCategoryTensorComparison_app_app (K M : DerivedCategory C) :
    (F.mapDerivedCategoryTensorComparison.app K).app M =
      F.leftDerivedFunctorIsoMapDerivedCategory.inv.app (K ⊗ M) ≫
        (F.leftDerivedTensorComparison.app K).app M ≫
          (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app K ⊗ₘ
            F.leftDerivedFunctorIsoMapDerivedCategory.hom.app M) := by
  simp [mapDerivedCategoryTensorComparison]

instance : IsIso F.mapDerivedCategoryTensorComparison := by
  dsimp only [mapDerivedCategoryTensorComparison]
  have : IsIso (tensorHomNatTrans F.leftDerivedFunctorIsoMapDerivedCategory.hom) := by
    have (X Y : DerivedCategory C) : IsIso
        (((tensorHomNatTrans F.leftDerivedFunctorIsoMapDerivedCategory.hom).app X).app Y) := by
      rw [tensorHomNatTrans_app_app]
      infer_instance
    have (X : DerivedCategory C) :
        IsIso ((tensorHomNatTrans F.leftDerivedFunctorIsoMapDerivedCategory.hom).app X) :=
      NatIso.isIso_of_isIso_app _
    exact NatIso.isIso_of_isIso_app _
  infer_instance

/-- On objects of the homotopy category, the comparison
`D(F)(Qh K ⊗ᴸ Qh M) ⟶ D(F)(Qh K) ⊗ᴸ D(F)(Qh M)` is induced by the comonoidal structure of `F`:
```
  D(F)(Qh K ⊗ᴸ Qh M) ──comparison──▶ D(F)(Qh K) ⊗ᴸ D(F)(Qh M)
          │                                    │
          ▼                                    ▼
   Qh(F(K ⊗ M)) ─────────Qh(δ F)──────▶ Qh(F K ⊗ F M)
```
-/
@[reassoc]
lemma mapDerivedCategoryTensorComparison_app_app_comp (K M : HomotopyCategory C (.up ℤ)) :
    (F.mapDerivedCategoryTensorComparison.app (Qh.obj K)).app (Qh.obj M) ≫
        (F.mapDerivedCategoryFactorsh.hom.app K ⊗ₘ F.mapDerivedCategoryFactorsh.hom.app M) ≫
          LaxMonoidal.μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj K)
            ((F.mapHomotopyCategory (.up ℤ)).obj M) =
      F.mapDerivedCategory.map (LaxMonoidal.μ Qh K M) ≫
        F.mapDerivedCategoryFactorsh.hom.app (K ⊗ M) ≫
          Qh.map (OplaxMonoidal.δ (F.mapHomotopyCategory (.up ℤ)) K M) := by
  have hfac (X : HomotopyCategory C (.up ℤ)) :
      F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (Qh.obj X) ≫
        F.mapDerivedCategoryFactorsh.hom.app X = F.leftDerivedFunctorCounit.app X :=
    NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac X
  have hfac' (X : HomotopyCategory C (.up ℤ)) :
      F.mapDerivedCategoryFactorsh.hom.app X =
        F.leftDerivedFunctorIsoMapDerivedCategory.inv.app (Qh.obj X) ≫
          F.leftDerivedFunctorCounit.app X := by
    rw [← hfac, Iso.inv_hom_id_app_assoc]
  rw [mapDerivedCategoryTensorComparison_app_app]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, hfac]
  rw [F.leftDerivedTensorComparison_app_app_comp_tensorHom, hfac' (K ⊗ M),
    ← NatTrans.naturality_assoc]
  simp only [Category.assoc]
  rfl

/-- The oplax monoidal structure on `D(F) : D(C) ⥤ D(D)` whose comonoidal structure is the
tensor comparison `CategoryTheory.Functor.mapDerivedCategoryTensorComparison`. It is induced by
the oplax monoidal structure of `F` on homotopy categories, computing on complexes whose image
under `F` is K-flat. -/
@[instance_reducible]
noncomputable def mapDerivedCategoryOplaxMonoidal : F.mapDerivedCategory.OplaxMonoidal :=
  haveI := DerivedCategory.isIso_ε_Qh D
  OplaxMonoidal.ofLaxSquare (Q₁ := Qh) (Q₂ := Qh) (F := F.mapHomotopyCategory (.up ℤ))
    F.mapDerivedCategoryTensorComparison (fun a ↦ F.mapDerivedCategoryFactorsh.hom.app a)
    (fun _ _ f ↦ F.mapDerivedCategoryFactorsh.hom.naturality f)
    F.mapDerivedCategoryTensorComparison_app_app_comp F.kFlatMap F.exists_kFlatMap_iso
    (fun x _ hb ↦ isIso_μNatTrans_Qh_app_app_of_kFlat x _ hb)

lemma mapDerivedCategoryOplaxMonoidal_δ (K M : DerivedCategory C) :
    letI := F.mapDerivedCategoryOplaxMonoidal
    OplaxMonoidal.δ F.mapDerivedCategory K M =
      (F.mapDerivedCategoryTensorComparison.app K).app M :=
  rfl

lemma isIso_mapDerivedCategoryOplaxMonoidal_η :
    letI := F.mapDerivedCategoryOplaxMonoidal
    IsIso (OplaxMonoidal.η F.mapDerivedCategory) := by
  have := DerivedCategory.isIso_ε_Qh C
  have := DerivedCategory.isIso_ε_Qh D
  have : IsIso (OplaxMonoidal.η (F.mapHomologicalComplex (.up ℤ))) := inferInstance
  have : IsIso (OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) := by
    rw [Functor.mapHomotopyCategory_η]
    exact Functor.map_isIso _ _
  exact inferInstanceAs (IsIso (F.mapDerivedCategory.map (LaxMonoidal.ε Qh) ≫
    F.mapDerivedCategoryFactorsh.hom.app (𝟙_ _) ≫
      Qh.map (OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) ≫
        CategoryTheory.inv (LaxMonoidal.ε Qh)))

/-- The comparison `D(F)(K ⊗ᴸ -) ⟶ D(F) K ⊗ᴸ D(F)(-)` for a fixed `K`. -/
noncomputable abbrev mapDerivedCategoryTensorComparisonApp (K : DerivedCategory C) :
    (curriedTensor _).obj K ⋙ F.mapDerivedCategory ⟶
      F.mapDerivedCategory ⋙ (curriedTensor _).obj (F.mapDerivedCategory.obj K) :=
  F.mapDerivedCategoryTensorComparison.app K

lemma commShift_mapDerivedCategoryTensorComparisonApp_of_iso {K K' : DerivedCategory C}
    (e : K ≅ K') [NatTrans.CommShift (F.mapDerivedCategoryTensorComparisonApp K') ℤ] :
    NatTrans.CommShift (F.mapDerivedCategoryTensorComparisonApp K) ℤ := by
  have eq : F.mapDerivedCategoryTensorComparisonApp K =
      whiskerRight ((curriedTensor _).map e.hom) F.mapDerivedCategory ≫
        F.mapDerivedCategoryTensorComparisonApp K' ≫
        whiskerLeft F.mapDerivedCategory
          ((curriedTensor _).map (F.mapDerivedCategory.map e.inv)) := by
    have := F.mapDerivedCategoryTensorComparison.naturality e.hom
    ext M
    have := congr_app this M
    dsimp at this ⊢
    rw [reassoc_of% this, ← comp_whiskerRight, ← Functor.map_comp, e.hom_inv_id,
      Functor.map_id, id_whiskerRight, Category.comp_id]
  rw [eq]
  infer_instance

lemma commShift_mapDerivedCategoryTensorComparisonApp_Qh_obj
    (X : HomotopyCategory C (.up ℤ)) (hX : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat X)
    (hFX : F.kFlatMap X) :
    NatTrans.CommShift (F.mapDerivedCategoryTensorComparisonApp (Qh.obj X)) ℤ :=
  DerivedCategory.commShift_of_tensorLeft_fac F F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh.hom X hX hFX _ (fun M ↦ by
      have := F.mapDerivedCategoryTensorComparison_app_app_comp X M
      rw [tensorHom_def, Category.assoc] at this
      exact this)

/-- For a fixed `K`, the comparison `D(F)(K ⊗ᴸ -) ⟶ D(F) K ⊗ᴸ D(F)(-)` commutes with the
shifts. -/
instance commShift_mapDerivedCategoryTensorComparisonApp (K : DerivedCategory C) :
    NatTrans.CommShift (F.mapDerivedCategoryTensorComparisonApp K) ℤ := by
  let Λ := (inferInstance : HasFunctorialFlatResolution C).some.reduced
  let K₀ := DerivedCategory.Q.objPreimage K
  let R := Λ.resolutionFunctor.obj K₀
  have hR := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K₀
  have hFR := F.kFlatMap_quotient_obj_resolutionFunctor_obj Λ K₀
  have := F.commShift_mapDerivedCategoryTensorComparisonApp_Qh_obj
    ((HomotopyCategory.quotient _ _).obj R) ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR)
    hFR
  let e : K ≅ Qh.obj ((HomotopyCategory.quotient _ _).obj R) :=
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app K₀))).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app R
  exact F.commShift_mapDerivedCategoryTensorComparisonApp_of_iso e

end CategoryTheory.Functor
