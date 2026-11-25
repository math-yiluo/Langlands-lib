/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# The left derived functor of a monoidal functor is monoidal

Let `F : C ⥤ D` be a strong monoidal functor between monoidal Grothendieck abelian categories
with functorial flat resolutions, which preserves flat objects and the quasi-isomorphisms between
K-flat complexes, and is a left adjoint; `F` need not be exact. The tensor comparison
`LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` of `CategoryTheory.Functor.leftDerivedTensorComparison` is the
comonoidal structure of a monoidal structure on `LF : D(C) ⥤ D(D)`. If moreover the comonoidal
structure of `F` is compatible with the braidings, then `LF` is braided for the Koszul braidings
`DerivedCategory.braidedCategory'`, hence preserves categorical traces. Finally, if `F` is
semilinear for a ring morphism `φ : R →+* S`, then so is `LF` on the endomorphisms `a • 𝟙`, and
the induced map on the endomorphisms of the unit sends `a • 𝟙` to `φ a • 𝟙`.

## Main definitions and results

- `CategoryTheory.Functor.leftDerivedFunctorMonoidal F`: the monoidal structure on `LF`, with
  comonoidal structure `F.leftDerivedTensorComparison` (`leftDerivedFunctorMonoidal_δ`).
- `CategoryTheory.Functor.leftDerivedFunctor_μ_map_braiding_hom`: the braided axiom for `LF`,
  and `CategoryTheory.Functor.leftDerivedFunctorBraided F hF`: the braided structure.
- `CategoryTheory.Functor.trace_leftDerivedFunctor_map`: `LF` preserves traces.
- `CategoryTheory.Functor.leftDerivedFunctor_map_smul_id` and
  `CategoryTheory.Functor.ε_comp_leftDerivedFunctor_map_smul_id_comp_η`: semilinearity.

## Implementation notes

The compatibility of the comonoidal structure of `G.mapHomotopyCategory` with the Koszul
braidings (`CategoryTheory.Functor.mapHomotopyCategory_map_braiding_hom_comp_δ`) is the same as
`CategoryTheory.Functor.mapHomotopyCategory_map_braiding_hom_δ` of
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided`, which is not imported
here because of its heavy dependencies on étale cohomology.
-/

@[expose] public section

universe u u₁ u₂

open CategoryTheory Category Abelian Limits MonoidalCategory DerivedCategory HomologicalComplex

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

section Braiding

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D)

open OplaxMonoidal in
/-- The compatibility `F β_{X, Y} ≫ δ_{Y, X} = δ_{X, Y} ≫ β_{F X, F Y}` of the comonoidal
structure of an oplax monoidal functor with the braidings is invariant under replacing `X` and
`Y` by isomorphic objects. -/
lemma OplaxMonoidal.map_braiding_hom_comp_δ_of_iso [F.OplaxMonoidal] {X X' Y Y' : C}
    (eX : X' ≅ X) (eY : Y' ≅ Y)
    (h : F.map (β_ X' Y').hom ≫ δ F Y' X' = δ F X' Y' ≫ (β_ (F.obj X') (F.obj Y')).hom) :
    F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
  rw [← cancel_epi (F.map (eX.hom ⊗ₘ eY.hom)), ← F.map_comp_assoc,
    BraidedCategory.braiding_naturality, F.map_comp_assoc, ← δ_natural, reassoc_of% h,
    ← δ_natural_assoc, BraidedCategory.braiding_naturality]

open LaxMonoidal OplaxMonoidal in
/-- For a monoidal functor, the compatibility of `δ` with the braidings implies the braided
axiom `μ_{X, Y} ≫ F β_{X, Y} = β_{F X, F Y} ≫ μ_{Y, X}`. -/
lemma Monoidal.μ_comp_map_braiding_hom_of_δ [F.Monoidal] (X Y : C)
    (h : F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom) :
    μ F X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X := by
  rw [← cancel_mono (δ F Y X), assoc, h, Monoidal.μ_δ_assoc, assoc, Monoidal.μ_δ, comp_id]

end Braiding

section HomotopyCategory

open OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [BraidedCategory C] [BraidedCategory D]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]

/-- If the comonoidal structure of an additive oplax monoidal functor `G` is compatible with the
braidings, then so is the comonoidal structure of `G` on cochain complexes, for the Koszul
braidings: on the summand `K.X p ⊗ L.X q` both sides are `(-1)^(pq)` times the corresponding
maps for `G`. -/
lemma OplaxMonoidal.mapHomologicalComplex_map_braiding_hom_comp_δNatTrans [G.OplaxMonoidal]
    (hG : ∀ X Y : C, G.map (β_ X Y).hom ≫ δ G Y X = δ G X Y ≫ (β_ (G.obj X) (G.obj Y)).hom)
    (K L : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map (β_ K L).hom ≫
        ((mapHomologicalComplexδNatTrans (.up ℤ) G).app L).app K =
      ((mapHomologicalComplexδNatTrans (.up ℤ) G).app K).app L ≫
        (β_ ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((G.mapHomologicalComplex (.up ℤ)).obj L)).hom := by
  ext n
  refine mapBifunctor.hom_ext_of_map G (fun p q h ↦ ?_)
  simp only [mapHomologicalComplexδNatTrans_app_app, comp_f, mapBifunctorComparison_f,
    Functor.mapHomologicalComplex_map_f]
  have h₁ := CochainComplex.Monoidal.ι_braiding_hom (K := K) (L := L) p q n h
  have h₂ := CochainComplex.Monoidal.ι_braiding_hom (K := (G.mapHomologicalComplex (.up ℤ)).obj K)
    (L := (G.mapHomologicalComplex (.up ℤ)).obj L) p q n h
  erw [← G.map_comp_assoc, h₁, map_ιMapBifunctor_mapBifunctorComparisonX_assoc, h₂]
  rw [G.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul, G.map_comp, assoc]
  erw [map_ιMapBifunctor_mapBifunctorComparisonX]
  simp only [mapBifunctorComparisonApp, δNatTrans_app_app]
  rw [reassoc_of% hG]
  rfl

/-- If the comonoidal structure of an additive monoidal functor `G` is compatible with the
braidings, then so is the comonoidal structure of `G.mapHomotopyCategory`, for the Koszul
braidings of the homotopy categories. -/
lemma mapHomotopyCategory_map_braiding_hom_comp_δ [G.Monoidal]
    (hG : ∀ X Y : C, G.map (β_ X Y).hom ≫ δ G Y X = δ G X Y ≫ (β_ (G.obj X) (G.obj Y)).hom)
    (K L : HomotopyCategory C (.up ℤ)) :
    (G.mapHomotopyCategory (.up ℤ)).map (β_ K L).hom ≫ δ (G.mapHomotopyCategory (.up ℤ)) L K =
      δ (G.mapHomotopyCategory (.up ℤ)) K L ≫
        (β_ ((G.mapHomotopyCategory (.up ℤ)).obj K)
          ((G.mapHomotopyCategory (.up ℤ)).obj L)).hom := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  have h := (HomotopyCategory.quotient D (.up ℤ)).congr_map
    (mapHomologicalComplex_map_braiding_hom_comp_δNatTrans G hG K L)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

end HomotopyCategory

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]

section Monoidal

open LaxMonoidal OplaxMonoidal

section Exact

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

omit [HasFunctorialFlatResolution D] [MonoidalClosed C] [BraidedCategory C] in
/-- The counit `LF (Qh K) ⟶ Qh (F K)` of the left derived functor of an exact functor is an
isomorphism. -/
instance isIso_leftDerivedFunctorCounit_app (K : HomotopyCategory C (.up ℤ)) :
    IsIso (F.leftDerivedFunctorCounit.app K) := by
  rw [← F.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac]
  infer_instance

variable [F.PreservesFlat] [F.IsLeftAdjoint]

omit [HasFunctorialFlatResolution D] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- Every object of `D(C)` is isomorphic to `Qh P` for a complex `P` whose image under `F` is
K-flat. -/
lemma exists_kFlatMap_iso (X : DerivedCategory C) :
    ∃ P, F.kFlatMap P ∧ Nonempty (Qh.obj P ≅ X) := by
  have := Localization.essSurj (Qh (C := C)) (HomotopyCategory.quasiIso _ (.up ℤ))
  obtain ⟨R⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
    (Φ := HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap) (Qh.objPreimage X)
  have : IsIso (Qh.map R.w) := Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property, ⟨asIso (Qh.map R.w) ≪≫ Qh.objObjPreimageIso X⟩⟩

end Exact

variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat] [F.IsLeftAdjoint]

omit [HasFunctorialFlatResolution D] [F.PreservesKFlatQuasiIso] in
/-- Every object of `D(C)` is isomorphic to `Qh P` for a K-flat complex `P` whose image under
`F` is K-flat. -/
lemma exists_kFlatKFlatMap_iso (X : DerivedCategory C) :
    ∃ P, F.kFlatKFlatMap P ∧ Nonempty (Qh.obj P ≅ X) := by
  have := Localization.essSurj (Qh (C := C)) (HomotopyCategory.quasiIso _ (.up ℤ))
  obtain ⟨R⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
    (Φ := HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatKFlatMap) (Qh.objPreimage X)
  have : IsIso (Qh.map R.w) := Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property, ⟨asIso (Qh.map R.w) ≪≫ Qh.objObjPreimageIso X⟩⟩

variable [F.Monoidal]

/-- The oplax monoidal structure on the left derived functor `LF : D(C) ⥤ D(D)` whose
comonoidal structure is the tensor comparison `F.leftDerivedTensorComparison`. It is induced by
the oplax monoidal structure of `F` on homotopy categories
(`CategoryTheory.Functor.mapHomotopyCategoryOplaxMonoidal`), computing on K-flat complexes whose
image under `F` is K-flat. -/
@[instance_reducible]
noncomputable def leftDerivedFunctorOplaxMonoidal : F.leftDerivedFunctor.OplaxMonoidal :=
  haveI := DerivedCategory.isIso_ε_Qh D
  OplaxMonoidal.ofLaxSquare' (Q₁ := Qh) (Q₂ := Qh) (F := F.mapHomotopyCategory (.up ℤ))
    F.leftDerivedTensorComparison (fun a ↦ F.leftDerivedFunctorCounit.app a)
    (fun _ _ f ↦ F.leftDerivedFunctorCounit.naturality f)
    F.leftDerivedTensorComparison_app_app_comp_tensorHom F.kFlatKFlatMap
    F.exists_kFlatKFlatMap_iso (fun a ha ↦ F.isIso_leftDerivedFunctorCounit_app_of_kFlat' a ha.1)
    (fun x _ hb ↦ isIso_μNatTrans_Qh_app_app_of_kFlat x _ hb.2)

lemma isIso_leftDerivedFunctorOplaxMonoidal_δ (X X' : DerivedCategory C) :
    letI := F.leftDerivedFunctorOplaxMonoidal
    IsIso (δ F.leftDerivedFunctor X X') :=
  inferInstanceAs (IsIso ((F.leftDerivedTensorComparison.app X).app X'))

lemma isIso_leftDerivedFunctorOplaxMonoidal_η :
    letI := F.leftDerivedFunctorOplaxMonoidal
    IsIso (η F.leftDerivedFunctor) := by
  have := DerivedCategory.isIso_ε_Qh D
  have := DerivedCategory.isIso_ε_Qh C
  have : IsIso (η (F.mapHomotopyCategory (.up ℤ))) := by
    rw [Functor.mapHomotopyCategory_η]
    infer_instance
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' (𝟙_ _)
    (ObjectProperty.prop_unit (HomotopyCategory.quasiIso C (.up ℤ)).kFlat)
  exact inferInstanceAs (IsIso (F.leftDerivedFunctor.map (ε Qh) ≫
    F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
      Qh.map (η (F.mapHomotopyCategory (.up ℤ))) ≫ CategoryTheory.inv (ε Qh)))

/-- The left derived functor `LF : D(C) ⥤ D(D)` of a monoidal functor as a monoidal
functor: the oplax monoidal structure `leftDerivedFunctorOplaxMonoidal`, whose structure maps are
isomorphisms. Its comonoidal structure is `F.leftDerivedTensorComparison`
(`CategoryTheory.Functor.leftDerivedFunctorMonoidal_δ`). -/
@[instance_reducible]
noncomputable def leftDerivedFunctorMonoidal : F.leftDerivedFunctor.Monoidal :=
  letI := F.leftDerivedFunctorOplaxMonoidal
  haveI := F.isIso_leftDerivedFunctorOplaxMonoidal_δ
  haveI := F.isIso_leftDerivedFunctorOplaxMonoidal_η
  (Functor.CoreMonoidal.ofOplaxMonoidal _).toMonoidal

/-- The comonoidal structure of the monoidal functor `LF` is the tensor comparison
`F.leftDerivedTensorComparison`. -/
lemma leftDerivedFunctorMonoidal_δ (K M : DerivedCategory C) :
    letI := F.leftDerivedFunctorMonoidal
    δ F.leftDerivedFunctor K M = (F.leftDerivedTensorComparison.app K).app M :=
  rfl

end Monoidal

section Braided

open LaxMonoidal OplaxMonoidal

omit [HasFunctorialFlatResolution D] [MonoidalClosed D] [BraidedCategory D] in
/-- The braiding `DerivedCategory.braidedCategory'` on objects `Qh K`, `Qh M`:
`β_{Qh K, Qh M} ≫ μ_{M, K} = μ_{K, M} ≫ Qh β_{K, M}`, where `β_{K, M}` is the Koszul braiding of
the homotopy category. -/
lemma _root_.DerivedCategory.braidedCategory'_braiding_hom_μ_Qh
    (K M : HomotopyCategory C (.up ℤ)) :
    letI := DerivedCategory.braidedCategory' C
    (β_ (Qh.obj K) (Qh.obj M)).hom ≫ μ Qh M K = μ Qh K M ≫ Qh.map (β_ K M).hom :=
  DerivedMonoidal.braiding_hom_μ Qh (HomotopyCategory.quasiIso C (.up ℤ)) K M

attribute [local instance] DerivedCategory.braidedCategory'

variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

/-- The comonoidal structure of `LF` is compatible with the derived braidings at `Qh P` and
`Qh Q`, when `F P` is K-flat and the counit of `LF` is an isomorphism at `P` and `Q` (for
instance when `F` is exact, or `P` and `Q` are K-flat). -/
lemma leftDerivedFunctor_map_braiding_hom_δ_Qh
    (hF : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (P Q : HomotopyCategory C (.up ℤ)) (hP : F.kFlatMap P)
    [IsIso (F.leftDerivedFunctorCounit.app P)] [IsIso (F.leftDerivedFunctorCounit.app Q)] :
    letI := F.leftDerivedFunctorMonoidal
    F.leftDerivedFunctor.map (β_ (Qh.obj P) (Qh.obj Q)).hom ≫
        δ F.leftDerivedFunctor (Qh.obj Q) (Qh.obj P) =
      δ F.leftDerivedFunctor (Qh.obj P) (Qh.obj Q) ≫
        (β_ (F.leftDerivedFunctor.obj (Qh.obj P)) (F.leftDerivedFunctor.obj (Qh.obj Q))).hom := by
  let := F.leftDerivedFunctorMonoidal
  have : IsIso (μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj Q)
      ((F.mapHomotopyCategory (.up ℤ)).obj P)) :=
    isIso_μNatTrans_Qh_app_app_of_kFlat _ _ hP
  rw [← cancel_mono ((F.leftDerivedFunctorCounit.app Q ⊗ₘ F.leftDerivedFunctorCounit.app P) ≫
    μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj Q) ((F.mapHomotopyCategory (.up ℤ)).obj P))]
  simp only [leftDerivedFunctorMonoidal_δ, assoc]
  have hβ : (β_ ((F.mapHomotopyCategory (.up ℤ) ⋙ Qh).obj P)
      ((F.mapHomotopyCategory (.up ℤ) ⋙ Qh).obj Q)).hom ≫
        μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj Q) ((F.mapHomotopyCategory (.up ℤ)).obj P) =
      μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj P) ((F.mapHomotopyCategory (.up ℤ)).obj Q) ≫
        Qh.map (β_ ((F.mapHomotopyCategory (.up ℤ)).obj P)
          ((F.mapHomotopyCategory (.up ℤ)).obj Q)).hom :=
    DerivedCategory.braidedCategory'_braiding_hom_μ_Qh _ _
  rw [leftDerivedTensorComparison_app_app_comp_tensorHom,
    ← BraidedCategory.braiding_naturality_assoc, hβ,
    leftDerivedTensorComparison_app_app_comp_tensorHom_assoc, ← Functor.map_comp_assoc,
    DerivedCategory.braidedCategory'_braiding_hom_μ_Qh P Q, Functor.map_comp_assoc]
  have hn : F.leftDerivedFunctor.map (Qh.map (β_ P Q).hom) ≫
      F.leftDerivedFunctorCounit.app (Q ⊗ P) =
      F.leftDerivedFunctorCounit.app (P ⊗ Q) ≫
        Qh.map ((F.mapHomotopyCategory (.up ℤ)).map (β_ P Q).hom) :=
    F.leftDerivedFunctorCounit.naturality _
  erw [reassoc_of% hn]
  rw [← Qh.map_comp, ← Qh.map_comp]
  congr 3
  exact mapHomotopyCategory_map_braiding_hom_comp_δ _ hF P Q

/-- The comonoidal structure of `LF` is compatible with the derived braidings
`DerivedCategory.braidedCategory'`: `LF β_{K, M} ≫ δ_{M, K} = δ_{K, M} ≫ β_{LF K, LF M}`, provided
the comonoidal structure of `F` is compatible with the braidings. -/
theorem leftDerivedFunctor_map_braiding_hom_δ
    (hF : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (K M : DerivedCategory C) :
    letI := F.leftDerivedFunctorMonoidal
    F.leftDerivedFunctor.map (β_ K M).hom ≫ δ F.leftDerivedFunctor M K =
      δ F.leftDerivedFunctor K M ≫
        (β_ (F.leftDerivedFunctor.obj K) (F.leftDerivedFunctor.obj M)).hom := by
  let := F.leftDerivedFunctorMonoidal
  obtain ⟨P, hP, ⟨eP⟩⟩ := F.exists_kFlatKFlatMap_iso K
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := F.exists_kFlatKFlatMap_iso M
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' P hP.1
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' Q hQ.1
  exact OplaxMonoidal.map_braiding_hom_comp_δ_of_iso _ eP eQ
    (F.leftDerivedFunctor_map_braiding_hom_δ_Qh hF P Q hP.2)

/-- **The left derived functor of a braided functor is braided.** For the monoidal
structure `CategoryTheory.Functor.leftDerivedFunctorMonoidal` of `LF` and the derived braidings
`DerivedCategory.braidedCategory'`, `μ_{K, M} ≫ LF β_{K, M} = β_{LF K, LF M} ≫ μ_{M, K}`. -/
theorem leftDerivedFunctor_μ_map_braiding_hom
    (hF : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (K M : DerivedCategory C) :
    letI := F.leftDerivedFunctorMonoidal
    μ F.leftDerivedFunctor K M ≫ F.leftDerivedFunctor.map (β_ K M).hom =
      (β_ (F.leftDerivedFunctor.obj K) (F.leftDerivedFunctor.obj M)).hom ≫
        μ F.leftDerivedFunctor M K := by
  let := F.leftDerivedFunctorMonoidal
  exact Monoidal.μ_comp_map_braiding_hom_of_δ _ K M
    (F.leftDerivedFunctor_map_braiding_hom_δ hF K M)

/-- The braided structure on the left derived functor `LF`, for the derived braidings
`DerivedCategory.braidedCategory'`, whose monoidal structure is
`CategoryTheory.Functor.leftDerivedFunctorMonoidal`. -/
@[instance_reducible]
noncomputable def leftDerivedFunctorBraided
    (hF : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom) :
    F.leftDerivedFunctor.Braided :=
  letI := F.leftDerivedFunctorMonoidal
  { braided := F.leftDerivedFunctor_μ_map_braiding_hom hF }

/-- **The left derived functor of a braided functor preserves traces.** For the monoidal
structure `CategoryTheory.Functor.leftDerivedFunctorMonoidal` of `LF` and the derived braidings
`DerivedCategory.braidedCategory'`, `tr(LF v) = ε ≫ LF(tr v) ≫ η` for an endomorphism `v` of a
dualizable object `P` of `D(C)` such that `LF P` is dualizable. -/
theorem trace_leftDerivedFunctor_map
    (hF : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    {P : DerivedCategory C} [HasRightDual P] [HasRightDual (F.leftDerivedFunctor.obj P)]
    (v : P ⟶ P) :
    letI := F.leftDerivedFunctorMonoidal
    trace (F.leftDerivedFunctor.map v) =
      ε F.leftDerivedFunctor ≫ F.leftDerivedFunctor.map (trace v) ≫ η F.leftDerivedFunctor := by
  let := F.leftDerivedFunctorBraided hF
  exact Functor.map_trace _ v

end Braided

section Linear

variable {R S : Type*} [Ring R] [Ring S] [CategoryTheory.Linear R C] [CategoryTheory.Linear S D]
  (φ : R →+* S)
  (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]

omit [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D] in
/-- If a functor `F` is semilinear for `φ : R →+* S` on the endomorphisms `a • 𝟙`, so is
its left derived functor `LF`: `LF (a • 𝟙 K) = φ a • 𝟙 (LF K)`. -/
lemma leftDerivedFunctor_map_smul_id
    (hF : ∀ (X : C) (a : R), F.map (a • 𝟙 X) = φ a • 𝟙 (F.obj X))
    (K : DerivedCategory C) (a : R) :
    F.leftDerivedFunctor.map (a • 𝟙 K) = φ a • 𝟙 (F.leftDerivedFunctor.obj K) := by
  -- on complexes
  have hC (P : CochainComplex C ℤ) :
      (F.mapHomologicalComplex (.up ℤ)).map (a • 𝟙 P) = φ a • 𝟙 _ := by
    ext n
    simp [hF]
  -- on the homotopy category
  have hK (P : HomotopyCategory C (.up ℤ)) :
      (F.mapHomotopyCategory (.up ℤ)).map (a • 𝟙 P) = φ a • 𝟙 _ := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    rw [← Functor.map_id, ← Functor.map_smul, Functor.mapHomotopyCategory_map, hC,
      Functor.map_smul, Functor.map_id]
    rfl
  -- on the image of a K-flat complex
  have hQ (P : HomotopyCategory C (.up ℤ)) (hP : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat P) :
      F.leftDerivedFunctor.map (a • 𝟙 (Qh.obj P)) = φ a • 𝟙 _ := by
    have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' P hP
    have e : a • 𝟙 (Qh.obj P) = Qh.map (a • 𝟙 P) := by
      rw [Functor.map_smul, Functor.map_id]
    rw [e, ← cancel_mono (F.leftDerivedFunctorCounit.app _)]
    erw [F.leftDerivedFunctorCounit.naturality]
    rw [Functor.comp_map, hK, Functor.map_smul, Functor.map_id, Linear.smul_comp,
      Linear.comp_smul, id_comp]
    erw [comp_id]
  -- every object is isomorphic to the image of a K-flat complex
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_kFlat_iso K
  have h : a • 𝟙 K = e.inv ≫ (a • 𝟙 _) ≫ e.hom := by
    rw [Linear.smul_comp, id_comp, Linear.comp_smul, e.inv_hom_id]
  rw [h, Functor.map_comp, Functor.map_comp, hQ P hP, Linear.smul_comp, id_comp, Linear.comp_smul,
    ← Functor.map_comp, e.inv_hom_id, Functor.map_id]

variable [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

open LaxMonoidal OplaxMonoidal in
/-- If a monoidal functor `F` is semilinear for `φ : R →+* S` on the endomorphisms `a • 𝟙`,
the induced map `f ↦ ε ≫ LF f ≫ η` on the endomorphisms of the unit of `D(C)` sends `a • 𝟙` to
`φ a • 𝟙`. -/
lemma ε_comp_leftDerivedFunctor_map_smul_id_comp_η
    (hF : ∀ (X : C) (a : R), F.map (a • 𝟙 X) = φ a • 𝟙 (F.obj X)) (a : R) :
    letI := F.leftDerivedFunctorMonoidal
    ε F.leftDerivedFunctor ≫ F.leftDerivedFunctor.map (a • 𝟙 (𝟙_ _)) ≫ η F.leftDerivedFunctor =
      φ a • 𝟙 (𝟙_ _) := by
  let := F.leftDerivedFunctorMonoidal
  rw [F.leftDerivedFunctor_map_smul_id φ hF, Linear.smul_comp, id_comp, Linear.comp_smul,
    Monoidal.ε_η]

end Linear

end CategoryTheory.Functor
