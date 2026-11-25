/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Equivalence

/-!
# Equivalences of abelian categories commuting with the tensor products

Let `F : C₁ ⥤ C₂` be an additive equivalence of monoidal closed braided Grothendieck abelian
categories with functorial flat resolutions, together with a natural isomorphism
`F(A ⊗ B) ≅ F A ⊗ F B` of bifunctors (no coherence with the associators or unitors is required).
Then `D(F)` commutes with the derived tensor products:
`D(F)(N ⊗ᴸ M) ≅ D(F) N ⊗ᴸ D(F) M`
(`DerivedCategory.tensorLeftCompMapDerivedCategoryIsoOfTensorIso`).

This generalises `DerivedCategory.tensorLeftCompMapDerivedCategoryIso`, which assumes `F`
monoidal.

## Main declarations

- `CategoryTheory.Functor.preservesFlat_of_isEquivalence_of_tensorIso`: such an `F` preserves
  flat objects.
- `DerivedCategory.mapHomotopyCategoryTensorHom`: the induced comparison
  `F(K ⊗ L) ⟶ F K ⊗ F L` on homotopy categories, an isomorphism.
- `DerivedCategory.tensorLeftCompMapDerivedCategoryIsoOfTensorIso`: the comparison of the
  derived tensor products, computed as in `DerivedCategory.tensorLeftCompMapDerivedCategoryIso`
  on a K-flat representative `P` of `N` with `F(P)` K-flat.
-/

@[expose] public section

universe w v

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

section

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- An equivalence of categories `F` together with a natural isomorphism of bifunctors
`F(A ⊗ B) ≅ F A ⊗ F B` preserves flat objects: tensoring with `F(X)` is, up to isomorphism, the
composite of `F⁻¹`, tensoring with `X` and `F`. No coherence of the isomorphism is needed. -/
lemma preservesFlat_of_isEquivalence_of_tensorIso (F : C ⥤ D) [F.IsEquivalence]
    (τ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D)) :
    F.PreservesFlat where
  flat_obj {X} hX := by
    have := hX.tensorLeft.preservesFiniteLimits
    have := hX.tensorLeft.preservesFiniteColimits
    have := hX.tensorRight.preservesFiniteLimits
    have := hX.tensorRight.preservesFiniteColimits
    have eL : F ⋙ tensorLeft (F.obj X) ≅ tensorLeft X ⋙ F :=
      NatIso.ofComponents (fun Y ↦ ((τ.app X).app Y).symm)
        (fun f ↦ (τ.inv.app X).naturality f)
    have eR : F ⋙ tensorRight (F.obj X) ≅ tensorRight X ⋙ F :=
      NatIso.ofComponents (fun Y ↦ ((τ.app Y).app X).symm)
        (fun f ↦ NatTrans.congr_app (τ.inv.naturality f) X)
    refine ⟨(exactFunctor _ _).prop_of_iso
      ((Functor.leftUnitor _).symm ≪≫ isoWhiskerRight F.asEquivalence.counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft F.inv eL).symm
      ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩),
      (exactFunctor _ _).prop_of_iso
      ((Functor.leftUnitor _).symm ≪≫ isoWhiskerRight F.asEquivalence.counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft F.inv eR).symm
      ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩)⟩

end

end CategoryTheory.Functor

namespace DerivedCategory

variable {C₁ C₂ : Type*} [Category.{v} C₁] [Abelian C₁] [IsGrothendieckAbelian.{w} C₁]
  [HasDerivedCategory.{w} C₁] [MonoidalCategory C₁] [MonoidalClosed C₁] [MonoidalPreadditive C₁]
  [BraidedCategory C₁] [Abelian.HasFunctorialFlatResolution C₁]
  [Category.{v} C₂] [Abelian C₂] [IsGrothendieckAbelian.{w} C₂]
  [HasDerivedCategory.{w} C₂] [MonoidalCategory C₂] [MonoidalClosed C₂] [MonoidalPreadditive C₂]
  [BraidedCategory C₂] [Abelian.HasFunctorialFlatResolution C₂]

local instance hasColimitsOfSize_equivalenceTensorIso₁ : HasColimitsOfSize.{0, 0} C₁ :=
  hasColimitsOfSizeShrink C₁
local instance hasColimitsOfSize_equivalenceTensorIso₂ : HasColimitsOfSize.{0, 0} C₂ :=
  hasColimitsOfSizeShrink C₂

variable (F : C₁ ⥤ C₂) [F.IsEquivalence] [F.Additive]
  (τ : (Functor.postcompose₂.obj F).obj (curriedTensor C₁) ≅
    (((Functor.whiskeringLeft₂ C₂).obj F).obj F).obj (curriedTensor C₂))

local instance additive_asEquivalence_functor_tensorIso : F.asEquivalence.functor.Additive :=
  ‹F.Additive›

/-- The natural transformation `F(A ⊗ B) ⟶ F(A) ⊗ F(B)` of homotopy categories induced by a
natural isomorphism `τ : F(A ⊗ B) ≅ F A ⊗ F B` of bifunctors: it is obtained from
`HomologicalComplex.mapBifunctorComparisonNatTrans τ.hom` by passing to the quotient. -/
noncomputable def mapHomotopyCategoryTensorHom :
    (Functor.postcompose₂.obj (F.mapHomotopyCategory (.up ℤ))).obj
        (curriedTensor (HomotopyCategory C₁ (.up ℤ))) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
        (F.mapHomotopyCategory (.up ℤ))).obj (curriedTensor (HomotopyCategory C₂ (.up ℤ))) :=
  Quotient.natTransLift₂' _ _
    ((Functor.postcompose₂.obj (HomotopyCategory.quotient C₂ (.up ℤ))).map
      (HomologicalComplex.mapBifunctorComparisonNatTrans τ.hom (.up ℤ)))

instance : IsIso (mapHomotopyCategoryTensorHom F τ) := by
  have (X Y : C₁) : IsIso ((τ.hom.app X).app Y) := inferInstanceAs (IsIso ((τ.app X).app Y).hom)
  have (K L : CochainComplex C₁ ℤ) : IsIso ((((Functor.postcompose₂.obj
      (HomotopyCategory.quotient C₂ (.up ℤ))).map
        (HomologicalComplex.mapBifunctorComparisonNatTrans τ.hom (.up ℤ))).app K).app L) :=
    Functor.map_isIso (HomotopyCategory.quotient C₂ (.up ℤ))
      (((HomologicalComplex.mapBifunctorComparisonNatTrans τ.hom (.up ℤ)).app K).app L)
  exact Quotient.isIso_natTransLift₂ _ _ _

/-- For a complex `P` of `C₁` such that both `P` and `F(P)` are K-flat, the functor `D(F)`
commutes with tensoring by `Qh P`: `D(F)(Qh P ⊗ᴸ M) ≅ D(F)(Qh P) ⊗ᴸ D(F) M`, naturally in `M`. -/
noncomputable def tensorLeftCompMapDerivedCategoryIsoOfKFlatOfTensorIso
    (P : HomotopyCategory C₁ (.up ℤ))
    (hP : (HomotopyCategory.quasiIso C₁ (.up ℤ)).kFlat P)
    (hFP : (HomotopyCategory.quasiIso C₂ (.up ℤ)).kFlat
      ((F.mapHomotopyCategory (.up ℤ)).obj P)) :
    (curriedTensor _).obj (Qh.obj P) ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ (curriedTensor _).obj (F.mapDerivedCategory.obj (Qh.obj P)) :=
  have := isIso_tensorLeftCounit P hP
  have := isIso_tensorLeftCounit _ hFP
  Localization.liftNatIso Qh (HomotopyCategory.quasiIso C₁ (.up ℤ))
    (Qh ⋙ ((curriedTensor _).obj (Qh.obj P) ⋙ F.mapDerivedCategory))
    (Qh ⋙ (F.mapDerivedCategory ⋙ (curriedTensor _).obj (F.mapDerivedCategory.obj (Qh.obj P))))
    _ _
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (asIso (tensorLeftCounit P)) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ F.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso ((mapHomotopyCategoryTensorHom F τ).app P)) Qh ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (asIso (tensorLeftCounit _)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactorsh.symm _ ≪≫
      Functor.isoWhiskerLeft _
        ((curriedTensor _).mapIso (F.mapDerivedCategoryFactorsh.app P).symm) ≪≫
      Functor.associator _ _ _)

omit [HasDerivedCategory C₂] [Abelian.HasFunctorialFlatResolution C₂] in
/-- Every object `N` of `D(C₁)` is isomorphic to `Qh P` for a complex `P` such that both `P`
and `F(P)` are K-flat: a functorial flat resolution of a representative of `N`. -/
lemma exists_kFlat_iso_of_isEquivalence_of_tensorIso
    (τ : (Functor.postcompose₂.obj F).obj (curriedTensor C₁) ≅
      (((Functor.whiskeringLeft₂ C₂).obj F).obj F).obj (curriedTensor C₂))
    (N : DerivedCategory C₁) :
    ∃ P : HomotopyCategory C₁ (.up ℤ), (HomotopyCategory.quasiIso C₁ (.up ℤ)).kFlat P ∧
      (HomotopyCategory.quasiIso C₂ (.up ℤ)).kFlat ((F.mapHomotopyCategory (.up ℤ)).obj P) ∧
      Nonempty (Qh.obj P ≅ N) := by
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C₁) := Classical.arbitrary _
  have := F.preservesFlat_of_isEquivalence_of_tensorIso τ
  let K := Q.objPreimage N
  refine ⟨(HomotopyCategory.quotient _ _).obj (Λ.reduced.resolutionFunctor.obj K),
    (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K),
    ObjectProperty.prop_of_iso _ ((F.mapHomotopyCategoryFactors (.up ℤ)).app _).symm
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2
        (F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ.reduced
          ObjectProperty.flat.essImage_ι_le K)),
    ⟨(quotientCompQhIso C₁).app _ ≪≫ asIso (Q.map (Λ.reduced.resolutionNatTrans.app K)) ≪≫
      Q.objObjPreimageIso N⟩⟩

/-- For an additive equivalence `F` with a natural isomorphism `τ : F(A ⊗ B) ≅ F A ⊗ F B`, the
functor `D(F)` commutes with tensoring on the left: `D(F)(N ⊗ᴸ M) ≅ D(F) N ⊗ᴸ D(F) M`,
naturally in `M`. -/
noncomputable def tensorLeftCompMapDerivedCategoryIsoOfTensorIso (N : DerivedCategory C₁) :
    (curriedTensor _).obj N ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ (curriedTensor _).obj (F.mapDerivedCategory.obj N) :=
  have h := exists_kFlat_iso_of_isEquivalence_of_tensorIso F τ N
  Functor.isoWhiskerRight ((curriedTensor _).mapIso h.choose_spec.2.2.some.symm) _ ≪≫
    tensorLeftCompMapDerivedCategoryIsoOfKFlatOfTensorIso F τ _ h.choose_spec.1
      h.choose_spec.2.1 ≪≫
    Functor.isoWhiskerLeft _ ((curriedTensor _).mapIso
      (F.mapDerivedCategory.mapIso h.choose_spec.2.2.some))

end DerivedCategory
