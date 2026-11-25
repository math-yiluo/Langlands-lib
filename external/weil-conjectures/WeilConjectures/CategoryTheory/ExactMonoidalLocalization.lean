/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal

/-! # Exact monoidal localization for specified derived-category models

The universal tensor comparison for an exact strong monoidal left adjoint, retaining
its counit square for the supplied `HasDerivedCategory` instances.
Source: Stacks 06YT, 07A4; the two-variable left derived universal property.
(blueprint: lem-sf-derived-exact-monoidal-localization).
-/

@[expose] public section

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory
open scoped CategoryTheory.Functor
set_option autoImplicit false
noncomputable section
universe u u₁ u₂
namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C] [HasDerivedCategory.{u + 1} C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D] [HasDerivedCategory.{u + 1} D]
local instance colimitsC : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C
local instance colimitsD : HasColimitsOfSize.{0, 0} D := hasColimitsOfSizeShrink D
/-- The lax monoidal structure `Qh K ⊗ᴸ Qh M ⟶ Qh (K ⊗ M)` of `Qh : K(C) ⥤ D(C)` is an
isomorphism when `M` is K-flat. -/
lemma specifiedModel_isIso_μNatTrans_Qh_app_app_of_kFlat (K M : HomotopyCategory C (.up ℤ))
    (hM : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat M) :
    IsIso (((LaxMonoidal.μNatTrans (Qh (C := C))).app K).app M) :=
  have := DerivedCategory.isLeftDerivedFunctor₂CurriedTensor C
  (MorphismProperty.id_prod_kFlat_derives_curriedTensor
    (HomotopyCategory.quasiIso C (.up ℤ)) Qh).isIso_of_isLeftDerivabilityStructure
      (LF := curriedTensor (DerivedCategory C)) (LaxMonoidal.μNatTrans Qh) K ⟨_, hM⟩

section Comparison

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The bifunctor `(K, M) ↦ LF K ⊗ᴸ LF M`, of type `D(C) ⥤ D(C) ⥤ D(D)`. -/
noncomputable abbrev specifiedModel_derivedTensorLeftDerived :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory D :=
  (((whiskeringLeft₂ _).obj F.mapDerivedCategory).obj F.mapDerivedCategory).obj
    (curriedTensor _)

/-- The bifunctor `(K, M) ↦ LF(K ⊗ᴸ M)`, of type `D(C) ⥤ D(C) ⥤ D(D)`. -/
noncomputable abbrev specifiedModel_leftDerivedDerivedTensor :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory D :=
  (postcompose₂.obj F.mapDerivedCategory).obj (curriedTensor _)

/-- The counit exhibiting `(K, M) ↦ LF K ⊗ᴸ LF M` as the total left derived functor of
`(A, B) ↦ F A ⊗ F B`. On `K, M` in `K(C)` it is the composite
```
 LF(Qh K) ⊗ᴸ LF(Qh M) --(counit ⊗ᴸ 1)--> Qh(F K) ⊗ᴸ LF(Qh M)
   --(1 ⊗ᴸ counit)--> Qh(F K) ⊗ᴸ Qh(F M) --(μ Qh)--> Qh(F K ⊗ F M)
```
of the counits of `LF` on both factors and the lax monoidal structure of
`Qh : K(D) ⥤ D(D)`. -/
noncomputable def specifiedModel_derivedTensorLeftDerivedCounit :
    (((whiskeringLeft₂ _).obj (Qh (C := C))).obj Qh).obj
        (specifiedModel_derivedTensorLeftDerived F) ⟶
      (((whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
        (F.mapHomotopyCategory (.up ℤ))).obj
          ((postcompose₂.obj Qh).obj (curriedTensor _)) :=
  (((whiskeringLeft₂ _).map F.mapDerivedCategoryFactorsh.hom).app
      (Qh ⋙ F.mapDerivedCategory)).app (curriedTensor _) ≫
    (((whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ) ⋙ Qh)).map
      F.mapDerivedCategoryFactorsh.hom).app (curriedTensor _) ≫
    (((whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
        (F.mapHomotopyCategory (.up ℤ))).map (LaxMonoidal.μNatTrans Qh)

/-- The counit exhibiting `(K, M) ↦ LF(K ⊗ᴸ M)` as the total left derived functor of
`(A, B) ↦ F(A ⊗ B)`. On `K, M` in `K(C)` it is the composite
```
 LF(Qh K ⊗ᴸ Qh M) --(LF(μ Qh))--> LF(Qh (K ⊗ M)) --(counit)--> Qh(F(K ⊗ M))
```
-/
noncomputable def specifiedModel_leftDerivedDerivedTensorCounit :
    (((whiskeringLeft₂ _).obj (Qh (C := C))).obj Qh).obj
        (specifiedModel_leftDerivedDerivedTensor F) ⟶
      (postcompose₂.obj (F.mapHomotopyCategory (.up ℤ) ⋙ Qh)).obj (curriedTensor _) :=
  (postcompose₂.obj F.mapDerivedCategory).map (LaxMonoidal.μNatTrans Qh) ≫
    (postcompose₂.map F.mapDerivedCategoryFactorsh.hom).app (curriedTensor _)

variable [F.PreservesFlat] [F.IsLeftAdjoint]

/-- `(K, M) ↦ LF K ⊗ᴸ LF M` is the total left derived functor of `(A, B) ↦ F A ⊗ F B`. It is
computed on pairs `(K, M)` with `K` K-flat and `M`, `F M` K-flat. -/
instance specifiedModel_isLeftDerivedFunctor₂_derivedTensorLeftDerived :
    (specifiedModel_derivedTensorLeftDerived F).IsLeftDerivedFunctor₂
      (specifiedModel_derivedTensorLeftDerivedCounit F)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatKFlatMap) _ (fun X₁ X₂ ↦ ?_)
  have hμ := specifiedModel_isIso_μNatTrans_Qh_app_app_of_kFlat
    ((F.mapHomotopyCategory _).obj X₁.obj) _ X₂.property.2
  have : IsIso (F.mapDerivedCategoryFactorsh.hom.app X₁.obj) := inferInstance
  have : IsIso (F.mapDerivedCategoryFactorsh.hom.app X₂.obj) := inferInstance
  simp only [specifiedModel_derivedTensorLeftDerivedCounit, NatTrans.comp_app]
  exact IsIso.comp_isIso'
    (inferInstanceAs (IsIso (F.mapDerivedCategoryFactorsh.hom.app X₁.obj ▷ _)))
    (IsIso.comp_isIso' (inferInstanceAs (IsIso (_ ◁ F.mapDerivedCategoryFactorsh.hom.app X₂.obj)))
      hμ)

/-- `(K, M) ↦ LF(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ F(A ⊗ B)`. It is
computed on pairs of K-flat complexes. -/
instance specifiedModel_isLeftDerivedFunctor₂_leftDerivedDerivedTensor :
    (specifiedModel_leftDerivedDerivedTensor F).IsLeftDerivedFunctor₂
      (specifiedModel_leftDerivedDerivedTensorCounit F)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun X₁ X₂ ↦ ?_)
  have := specifiedModel_isIso_μNatTrans_Qh_app_app_of_kFlat X₁.obj _ X₂.property
  have : IsIso (F.mapDerivedCategoryFactorsh.hom.app (X₁.obj ⊗ X₂.obj)) := inferInstance
  simp only [specifiedModel_leftDerivedDerivedTensorCounit, NatTrans.comp_app]
  exact IsIso.comp_isIso'
    (Functor.map_isIso F.mapDerivedCategory (((LaxMonoidal.μNatTrans Qh).app X₁.obj).app X₂.obj))
    (inferInstanceAs (IsIso (F.mapDerivedCategoryFactorsh.hom.app (X₁.obj ⊗ X₂.obj))))

variable [F.Monoidal]

/-- The comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` of bifunctors `D(C) ⥤ D(C) ⥤ D(D)`, obtained by
deriving the comonoidal structure `δ` of `F`. It is the unique natural transformation such
that, for `K, M` in `K(C)`, the square
```
  LF(Qh K ⊗ᴸ Qh M) ──comparison──▶ LF(Qh K) ⊗ᴸ LF(Qh M)
          │                                │
          ▼                                ▼
     Qh(F(K ⊗ M)) ──────Qh(δ F)─────▶ Qh(F K ⊗ F M)
```
commutes, the vertical arrows being `specifiedModel_leftDerivedDerivedTensorCounit` and
`specifiedModel_derivedTensorLeftDerivedCounit`. -/
noncomputable def specifiedModel_leftDerivedTensorComparison :
    specifiedModel_leftDerivedDerivedTensor F ⟶ specifiedModel_derivedTensorLeftDerived F :=
  leftDerived₂NatTrans _ (specifiedModel_derivedTensorLeftDerivedCounit F)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (specifiedModel_leftDerivedDerivedTensorCounit F)
    (postcompose₂MapWhiskeringLeft₂ (OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F) Qh)

/-- The characterising property of `specifiedModel_leftDerivedTensorComparison`. -/
@[reassoc]
lemma specifiedModel_leftDerivedTensorComparison_app_app_comp_counit
    (K M : HomotopyCategory C (.up ℤ)) :
    ((F.specifiedModel_leftDerivedTensorComparison.app (Qh.obj K)).app (Qh.obj M)) ≫
        ((specifiedModel_derivedTensorLeftDerivedCounit F).app K).app M =
      ((specifiedModel_leftDerivedDerivedTensorCounit F).app K).app M ≫
        Qh.map (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app K).app M) :=
  leftDerived₂NatTrans_app_app _ _ _ _ _ _ _ K M

/-- The comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` is an isomorphism, `F` being strong monoidal. -/
instance specifiedModel_isIso_leftDerivedTensorComparison :
    IsIso F.specifiedModel_leftDerivedTensorComparison := by
  dsimp only [specifiedModel_leftDerivedTensorComparison]
  infer_instance

/-- `specifiedModel_leftDerivedTensorComparison` on objects of `K(C)`, through the factorization
isomorphisms `D(F) ∘ Qh ≅ Qh ∘ K(F)`. -/
lemma specifiedModel_comparison_fac (K M : HomotopyCategory C (.up ℤ)) :
    (F.specifiedModel_leftDerivedTensorComparison.app (Qh.obj K)).app (Qh.obj M) ≫
        (F.mapDerivedCategoryFactorsh.hom.app K ⊗ₘ
          F.mapDerivedCategoryFactorsh.hom.app M) ≫
        LaxMonoidal.μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj K)
          ((F.mapHomotopyCategory (.up ℤ)).obj M) =
      F.mapDerivedCategory.map (LaxMonoidal.μ Qh K M) ≫
        F.mapDerivedCategoryFactorsh.hom.app (K ⊗ M) ≫
        Qh.map (OplaxMonoidal.δ (F.mapHomotopyCategory (.up ℤ)) K M) := by
  have h := F.specifiedModel_leftDerivedTensorComparison_app_app_comp_counit K M
  simpa [specifiedModel_derivedTensorLeftDerivedCounit,
    specifiedModel_leftDerivedDerivedTensorCounit,
    tensorHom_def, Category.assoc, Functor.mapHomotopyCategory_δ] using h

omit [HasFunctorialFlatResolution D] [HasDerivedCategory D] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.Monoidal] in
/-- Every object of `D(C)` is isomorphic to `Qh P` for a complex `P` with `F P` K-flat. -/
lemma specifiedModel_exists_kFlatMap_iso (X : DerivedCategory C) :
    ∃ P, F.kFlatMap P ∧ Nonempty (Qh.obj P ≅ X) := by
  have := Localization.essSurj (Qh (C := C)) (HomotopyCategory.quasiIso _ (.up ℤ))
  obtain ⟨R⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
    (Φ := HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap) (Qh.objPreimage X)
  have : IsIso (Qh.map R.w) := Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property, ⟨asIso (Qh.map R.w) ≪≫ Qh.objObjPreimageIso X⟩⟩

/-- The oplax monoidal structure on `D(F)` whose comonoidal structure is
`specifiedModel_leftDerivedTensorComparison`. -/
@[instance_reducible]
def specifiedModel_oplax : F.mapDerivedCategory.OplaxMonoidal :=
  haveI := DerivedCategory.isIso_ε_Qh D
  OplaxMonoidal.ofLaxSquare (Q₁ := Qh) (Q₂ := Qh) (F := F.mapHomotopyCategory (.up ℤ))
    F.specifiedModel_leftDerivedTensorComparison (fun a ↦ F.mapDerivedCategoryFactorsh.hom.app a)
    (fun _ _ f ↦ F.mapDerivedCategoryFactorsh.hom.naturality f)
    F.specifiedModel_comparison_fac F.kFlatMap F.specifiedModel_exists_kFlatMap_iso
    (fun x _ hb ↦ specifiedModel_isIso_μNatTrans_Qh_app_app_of_kFlat x _ hb)

/-- The counit of `specifiedModel_oplax` is an isomorphism. -/
lemma specifiedModel_unit_iso :
    letI := F.specifiedModel_oplax
    IsIso (OplaxMonoidal.η F.mapDerivedCategory) := by
  have := DerivedCategory.isIso_ε_Qh C
  have := DerivedCategory.isIso_ε_Qh D
  have : IsIso (OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) := by
    rw [Functor.mapHomotopyCategory_η]
    exact Functor.map_isIso _ _
  exact inferInstanceAs (IsIso (F.mapDerivedCategory.map (LaxMonoidal.ε Qh) ≫
    F.mapDerivedCategoryFactorsh.hom.app (𝟙_ _) ≫
    Qh.map (OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) ≫
      CategoryTheory.inv (LaxMonoidal.ε Qh)))

/-- The functor `D(F)` induced on the specified derived categories by an exact monoidal
left adjoint `F` preserving flat objects, as a strong monoidal functor. -/
@[instance_reducible]
def specifiedModel_monoidal : F.mapDerivedCategory.Monoidal := by
  letI := F.specifiedModel_oplax
  haveI := F.specifiedModel_unit_iso
  haveI (X Y : DerivedCategory C) :
      IsIso (OplaxMonoidal.δ F.mapDerivedCategory X Y) :=
    inferInstanceAs (IsIso ((F.specifiedModel_leftDerivedTensorComparison.app X).app Y))
  exact Functor.Monoidal.ofOplaxMonoidal _

attribute [local instance] DerivedCategory.braidedCategory'

/-- `specifiedModel_braid` on objects `Qh P`, `Qh Q` with `F P` K-flat. -/
lemma specifiedModel_braid_Qh
    (hF : ∀ X Y : C, F.map (β_ X Y).hom ≫ OplaxMonoidal.δ F Y X =
      OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (P Q : HomotopyCategory C (.up ℤ)) (hP : F.kFlatMap P) :
    letI := F.specifiedModel_monoidal
    F.mapDerivedCategory.map (β_ (Qh.obj P) (Qh.obj Q)).hom ≫
        OplaxMonoidal.δ F.mapDerivedCategory (Qh.obj Q) (Qh.obj P) =
      OplaxMonoidal.δ F.mapDerivedCategory (Qh.obj P) (Qh.obj Q) ≫
        (β_ (F.mapDerivedCategory.obj (Qh.obj P))
          (F.mapDerivedCategory.obj (Qh.obj Q))).hom := by
  let := F.specifiedModel_monoidal
  have : IsIso (LaxMonoidal.μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj Q)
      ((F.mapHomotopyCategory (.up ℤ)).obj P)) :=
    specifiedModel_isIso_μNatTrans_Qh_app_app_of_kFlat _ _ hP
  rw [← cancel_mono ((F.mapDerivedCategoryFactorsh.hom.app Q ⊗ₘ
    F.mapDerivedCategoryFactorsh.hom.app P) ≫
    LaxMonoidal.μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj Q)
      ((F.mapHomotopyCategory (.up ℤ)).obj P))]
  simp only [Category.assoc]
  change F.mapDerivedCategory.map _ ≫
      (F.specifiedModel_leftDerivedTensorComparison.app _).app _ ≫ _ ≫ _ =
    (F.specifiedModel_leftDerivedTensorComparison.app _).app _ ≫ _ ≫ _ ≫ _
  have hβ : (β_ ((F.mapHomotopyCategory (.up ℤ) ⋙ Qh).obj P)
      ((F.mapHomotopyCategory (.up ℤ) ⋙ Qh).obj Q)).hom ≫
        LaxMonoidal.μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj Q)
          ((F.mapHomotopyCategory (.up ℤ)).obj P) =
      LaxMonoidal.μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj P)
        ((F.mapHomotopyCategory (.up ℤ)).obj Q) ≫
      Qh.map (β_ ((F.mapHomotopyCategory (.up ℤ)).obj P)
        ((F.mapHomotopyCategory (.up ℤ)).obj Q)).hom :=
    DerivedMonoidal.braiding_hom_μ Qh (HomotopyCategory.quasiIso D (.up ℤ)) _ _
  have hloc : (β_ (Qh.obj P) (Qh.obj Q)).hom ≫ LaxMonoidal.μ Qh Q P =
      LaxMonoidal.μ Qh P Q ≫ Qh.map (β_ P Q).hom :=
    DerivedMonoidal.braiding_hom_μ Qh (HomotopyCategory.quasiIso C (.up ℤ)) P Q
  rw [specifiedModel_comparison_fac, ← BraidedCategory.braiding_naturality_assoc, hβ,
    reassoc_of% specifiedModel_comparison_fac,
    ← Functor.map_comp_assoc, hloc, Functor.map_comp_assoc]
  have hn := F.mapDerivedCategoryFactorsh.hom.naturality (β_ P Q).hom
  rw [reassoc_of% hn, ← Qh.map_comp, ← Qh.map_comp]
  congr 3
  exact mapHomotopyCategory_map_braiding_hom_comp_δ _ hF P Q

/-- The comonoidal structure of `specifiedModel_monoidal` is compatible with the derived
braidings, provided the comonoidal structure of `F` is compatible with the braidings. -/
lemma specifiedModel_braid
    (hF : ∀ X Y : C, F.map (β_ X Y).hom ≫ OplaxMonoidal.δ F Y X =
      OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (K M : DerivedCategory C) :
    letI := F.specifiedModel_monoidal
    F.mapDerivedCategory.map (β_ K M).hom ≫ OplaxMonoidal.δ F.mapDerivedCategory M K =
      OplaxMonoidal.δ F.mapDerivedCategory K M ≫
        (β_ (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj M)).hom := by
  let := F.specifiedModel_monoidal
  obtain ⟨P, hP, ⟨eP⟩⟩ := F.specifiedModel_exists_kFlatMap_iso K
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := F.specifiedModel_exists_kFlatMap_iso M
  exact OplaxMonoidal.map_braiding_hom_comp_δ_of_iso _ eP eQ
    (F.specifiedModel_braid_Qh hF P Q hP)

end Comparison
end CategoryTheory.Functor
