/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering

/-!
# The tensor comparison of the left derived functor of a monoidal functor

Let `F : C ⥤ D` be a strong monoidal functor between monoidal Grothendieck abelian categories
with functorial flat resolutions, which preserves flat objects, `ℤ`-indexed colimits and the
quasi-isomorphisms between K-flat complexes (for instance an exact functor). We show that the
bifunctors `(K, M) ↦ LF(K ⊗ᴸ M)` and `(K, M) ↦ LF K ⊗ᴸ LF M` are the total left derived functors
of `(A, B) ↦ F(A ⊗ B)` and `(A, B) ↦ F A ⊗ F B`, and derive the comonoidal structure `δ` of `F`
into a natural isomorphism
`LF(K ⊗ᴸ M) ≅ LF K ⊗ᴸ LF M`.

This is the common generalisation of the tensor comparisons of the derived pullbacks
`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison` and
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`, which are its instances, and
it applies as well to the comparison functor between étale and pro-étale sheaves.

Both are computed on K-flat complexes `P` whose image `F P` is K-flat
(`CategoryTheory.Functor.kFlatKFlatMap`), on which the counit of `LF` is an isomorphism.

We then show that this comparison is compatible with the composition of exact functors and with
monoidal natural isomorphisms.

## Main definitions and results

- `CategoryTheory.Functor.kFlatMap F`: the complexes whose image under `F` is K-flat; they
  form a left derivability structure.
- `CategoryTheory.Functor.kFlatKFlatMap F`: the K-flat complexes whose image under `F` is
  K-flat; they form a left derivability structure.
- `CategoryTheory.Functor.leftDerivedTensorComparison F`: the comparison
  `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M`, an isomorphism.
- `CategoryTheory.Functor.leftDerivedTensorComparison_comp`: the comparison of `F ⋙ G` is the
  comparison of `F` followed by the comparison of `G`.
- `CategoryTheory.Functor.leftDerivedTensorComparison_of_iso`: a monoidal natural isomorphism
  `F ≅ F'` carries the comparison of `F` to the one of `F'`.
-/

@[expose] public section

universe u u₁ u₂ u₃ u₄

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]

section

variable (F : C ⥤ D) [F.Additive]

/-- The complexes in `K(C)` whose image under `F : C ⥤ D` is K-flat: the inverse image of the
K-flat complexes of `K(D)` under `K(F) : K(C) ⥤ K(D)`. -/
abbrev kFlatMap : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (HomotopyCategory.quasiIso D (.up ℤ)).kFlat.inverseImage (F.mapHomotopyCategory (.up ℤ))

variable [F.PreservesFlat] [PreservesColimitsOfShape ℤ F]

omit [HasFunctorialFlatResolution C] [HasFunctorialFlatResolution D] in
/-- A functor preserving flat objects and `ℤ`-indexed colimits sends the functorial flat
resolutions to K-flat complexes. -/
lemma kFlatMap_quotient_obj_resolutionFunctor_obj
    (Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ C)) [Λ.F.PreservesZeroMorphisms]
    (K : CochainComplex C ℤ) :
    F.kFlatMap ((HomotopyCategory.quotient _ _).obj (Λ.resolutionFunctor.obj K)) :=
  ObjectProperty.prop_of_iso (HomotopyCategory.quasiIso D (.up ℤ)).kFlat
    ((F.mapHomotopyCategoryFactors (.up ℤ)).app (Λ.resolutionFunctor.obj K)).symm
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2
      (F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ
        ObjectProperty.flat.essImage_ι_le K))

/-- The complexes whose image under `F` is K-flat form a left derivability structure on
`K(C)` for the quasi-isomorphisms. -/
instance isLeftDerivabilityStructure_kFlatMap :
    (HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap).IsLeftDerivabilityStructure :=
  let Λ := (inferInstance : HasFunctorialFlatResolution C).some
  HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism _
    Λ.reduced.resolutionNatTrans (fun _ ↦ inferInstance)
    (F.kFlatMap_quotient_obj_resolutionFunctor_obj Λ.reduced)

/-- The K-flat complexes in `K(C)` whose image under `F : C ⥤ D` is K-flat. -/
abbrev kFlatKFlatMap : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (HomotopyCategory.quasiIso C (.up ℤ)).kFlat ⊓ F.kFlatMap

/-- The K-flat complexes whose image under `F` is K-flat form a left derivability structure on
`K(C)` for the quasi-isomorphisms: the functorial flat resolutions are such complexes. -/
instance isLeftDerivabilityStructure_kFlatKFlatMap :
    (HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatKFlatMap).IsLeftDerivabilityStructure :=
  let Λ := (inferInstance : HasFunctorialFlatResolution C).some
  HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism _
    Λ.reduced.resolutionNatTrans (fun _ ↦ inferInstance)
    (fun K ↦ ⟨(HomotopyCategory.kFlat_quotient_obj_iff _).2
      (Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K),
      F.kFlatMap_quotient_obj_resolutionFunctor_obj Λ.reduced K⟩)

end

/-- The lax monoidal structure `Qh K ⊗ᴸ Qh M ⟶ Qh (K ⊗ M)` of `Qh : K(C) ⥤ D(C)` is an
isomorphism when `M` is K-flat. -/
lemma isIso_μNatTrans_Qh_app_app_of_kFlat (K M : HomotopyCategory C (.up ℤ))
    (hM : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat M) :
    IsIso (((LaxMonoidal.μNatTrans (Qh (C := C))).app K).app M) :=
  have := DerivedCategory.isLeftDerivedFunctor₂CurriedTensor C
  (MorphismProperty.id_prod_kFlat_derives_curriedTensor
    (HomotopyCategory.quasiIso C (.up ℤ)) Qh).isIso_of_isLeftDerivabilityStructure
      (LF := curriedTensor (DerivedCategory C)) (LaxMonoidal.μNatTrans Qh) K ⟨_, hM⟩

section Comparison

variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]

/-- The bifunctor `(K, M) ↦ LF K ⊗ᴸ LF M`, of type `D(C) ⥤ D(C) ⥤ D(D)`. -/
noncomputable abbrev derivedTensorLeftDerived :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory D :=
  (((whiskeringLeft₂ _).obj F.leftDerivedFunctor).obj F.leftDerivedFunctor).obj
    (curriedTensor _)

/-- The bifunctor `(K, M) ↦ LF(K ⊗ᴸ M)`, of type `D(C) ⥤ D(C) ⥤ D(D)`. -/
noncomputable abbrev leftDerivedDerivedTensor :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory D :=
  (postcompose₂.obj F.leftDerivedFunctor).obj (curriedTensor _)

/-- The counit exhibiting `(K, M) ↦ LF K ⊗ᴸ LF M` as the total left derived functor of
`(A, B) ↦ F A ⊗ F B`. On `K, M` in `K(C)` it is the composite
```
 LF(Qh K) ⊗ᴸ LF(Qh M) --(counit ⊗ᴸ 1)--> Qh(F K) ⊗ᴸ LF(Qh M)
   --(1 ⊗ᴸ counit)--> Qh(F K) ⊗ᴸ Qh(F M) --(μ Qh)--> Qh(F K ⊗ F M)
```
of the counits of `LF` on both factors and the lax monoidal structure of
`Qh : K(D) ⥤ D(D)`. -/
noncomputable def derivedTensorLeftDerivedCounit :
    (((whiskeringLeft₂ _).obj (Qh (C := C))).obj Qh).obj (derivedTensorLeftDerived F) ⟶
      (((whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
        (F.mapHomotopyCategory (.up ℤ))).obj
          ((postcompose₂.obj Qh).obj (curriedTensor _)) :=
  (((whiskeringLeft₂ _).map F.leftDerivedFunctorCounit).app
      (Qh ⋙ F.leftDerivedFunctor)).app (curriedTensor _) ≫
    (((whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ) ⋙ Qh)).map
      F.leftDerivedFunctorCounit).app (curriedTensor _) ≫
    (((whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
        (F.mapHomotopyCategory (.up ℤ))).map (LaxMonoidal.μNatTrans Qh)

/-- The counit exhibiting `(K, M) ↦ LF(K ⊗ᴸ M)` as the total left derived functor of
`(A, B) ↦ F(A ⊗ B)`. On `K, M` in `K(C)` it is the composite
```
 LF(Qh K ⊗ᴸ Qh M) --(LF(μ Qh))--> LF(Qh (K ⊗ M)) --(counit)--> Qh(F(K ⊗ M))
```
-/
noncomputable def leftDerivedDerivedTensorCounit :
    (((whiskeringLeft₂ _).obj (Qh (C := C))).obj Qh).obj (leftDerivedDerivedTensor F) ⟶
      (postcompose₂.obj (F.mapHomotopyCategory (.up ℤ) ⋙ Qh)).obj (curriedTensor _) :=
  (postcompose₂.obj F.leftDerivedFunctor).map (LaxMonoidal.μNatTrans Qh) ≫
    (postcompose₂.map F.leftDerivedFunctorCounit).app (curriedTensor _)

omit [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D] in
/-- On a K-flat object of `K(C)`, the counit of the total left derived functor of `F` is an
isomorphism. -/
lemma isIso_leftDerivedFunctorCounit_app_of_kFlat' (K : HomotopyCategory C (.up ℤ))
    (hK : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat K) :
    IsIso (F.leftDerivedFunctorCounit.app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  exact F.isIso_leftDerivedFunctorCounit_app_of_kFlat K
    ((HomotopyCategory.kFlat_quotient_obj_iff K).1 hK)

variable [F.PreservesFlat] [F.IsLeftAdjoint]

/-- `(K, M) ↦ LF K ⊗ᴸ LF M` is the total left derived functor of `(A, B) ↦ F A ⊗ F B`. It is
computed on pairs `(K, M)` with `K` K-flat and `M`, `F M` K-flat. -/
instance isLeftDerivedFunctor₂_derivedTensorLeftDerived :
    (derivedTensorLeftDerived F).IsLeftDerivedFunctor₂ (derivedTensorLeftDerivedCounit F)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatKFlatMap) _ (fun X₁ X₂ ↦ ?_)
  have hμ := isIso_μNatTrans_Qh_app_app_of_kFlat
    ((F.mapHomotopyCategory _).obj X₁.obj) _ X₂.property.2
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ X₁.property
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ X₂.property.1
  simp only [derivedTensorLeftDerivedCounit, NatTrans.comp_app]
  exact IsIso.comp_isIso'
    (inferInstanceAs (IsIso (F.leftDerivedFunctorCounit.app X₁.obj ▷ _)))
    (IsIso.comp_isIso' (inferInstanceAs (IsIso (_ ◁ F.leftDerivedFunctorCounit.app X₂.obj)))
      hμ)

/-- `(K, M) ↦ LF(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ F(A ⊗ B)`. It is
computed on pairs of K-flat complexes. -/
instance isLeftDerivedFunctor₂_leftDerivedDerivedTensor :
    (leftDerivedDerivedTensor F).IsLeftDerivedFunctor₂ (leftDerivedDerivedTensorCounit F)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun X₁ X₂ ↦ ?_)
  have := isIso_μNatTrans_Qh_app_app_of_kFlat X₁.obj _ X₂.property
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' _
    ((HomotopyCategory.quasiIso C (.up ℤ)).kFlat.prop_tensor X₁.property X₂.property)
  simp only [leftDerivedDerivedTensorCounit, NatTrans.comp_app]
  exact IsIso.comp_isIso'
    (Functor.map_isIso F.leftDerivedFunctor (((LaxMonoidal.μNatTrans Qh).app X₁.obj).app X₂.obj))
    (inferInstanceAs (IsIso (F.leftDerivedFunctorCounit.app (X₁.obj ⊗ X₂.obj))))

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
commutes, the vertical arrows being `leftDerivedDerivedTensorCounit` and
`derivedTensorLeftDerivedCounit`. -/
noncomputable def leftDerivedTensorComparison :
    leftDerivedDerivedTensor F ⟶ derivedTensorLeftDerived F :=
  leftDerived₂NatTrans _ (derivedTensorLeftDerivedCounit F)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedDerivedTensorCounit F)
    (postcompose₂MapWhiskeringLeft₂ (OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F) Qh)

/-- The characterising property of `leftDerivedTensorComparison`. -/
@[reassoc]
lemma leftDerivedTensorComparison_app_app_comp_counit (K M : HomotopyCategory C (.up ℤ)) :
    ((F.leftDerivedTensorComparison.app (Qh.obj K)).app (Qh.obj M)) ≫
        ((derivedTensorLeftDerivedCounit F).app K).app M =
      ((leftDerivedDerivedTensorCounit F).app K).app M ≫
        Qh.map (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app K).app M) :=
  leftDerived₂NatTrans_app_app _ _ _ _ _ _ _ K M

/-- The comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` is an isomorphism, `F` being strong monoidal. -/
instance isIso_leftDerivedTensorComparison : IsIso F.leftDerivedTensorComparison := by
  dsimp only [leftDerivedTensorComparison]
  infer_instance

end Comparison

section ComplexLevel

open OplaxMonoidal LaxMonoidal

variable {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
  [HasFunctorialFlatResolution E]

omit [HasFunctorialFlatResolution C] [HasFunctorialFlatResolution D]
  [HasFunctorialFlatResolution E] in
open HomologicalComplex in
/-- The comonoidal comparison `(F ⋙ G)(K ⊗ L) ⟶ (F ⋙ G) K ⊗ (F ⋙ G) L` of complexes is the
comparison of `F` followed by the comparison of `G`. -/
lemma mapHomologicalComplexδNatTrans_comp (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] [F.OplaxMonoidal] [G.OplaxMonoidal]
    (K L : CochainComplex C ℤ) :
    ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) (F ⋙ G)).app K).app L =
      (G.mapHomologicalComplex _).map
          (((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app K).app L) ≫
        ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app
          ((F.mapHomologicalComplex _).obj K)).app ((F.mapHomologicalComplex _).obj L) := by
  ext n
  refine mapBifunctor.hom_ext_of_map (F ⋙ G) (fun i₁ i₂ h ↦ ?_)
  simp only [OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app, mapBifunctorComparison_f,
    comp_f, Functor.mapHomologicalComplex_map_f, map_ιMapBifunctor_mapBifunctorComparisonX]
  erw [Functor.comp_map, ← G.map_comp_assoc, map_ιMapBifunctor_mapBifunctorComparisonX,
    G.map_comp_assoc, map_ιMapBifunctor_mapBifunctorComparisonX]
  simp
  rfl

omit [HasFunctorialFlatResolution C] [HasFunctorialFlatResolution D] in
open HomologicalComplex in
/-- A monoidal natural transformation `τ : F ⟶ F'` commutes with the comonoidal comparisons
of complexes. -/
lemma mapHomologicalComplexδNatTrans_naturality {F F' : C ⥤ D} [F.Additive] [F'.Additive]
    [F.IsLeftAdjoint] [F'.IsLeftAdjoint] [F.Monoidal] [F'.Monoidal] (τ : F ⟶ F')
    [NatTrans.IsMonoidal τ] (K L : CochainComplex C ℤ) :
    (NatTrans.mapHomologicalComplex τ (.up ℤ)).app (K ⊗ L) ≫
        ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F').app K).app L =
      ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app K).app L ≫
        ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K ⊗ₘ
          (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L) := by
  ext n
  refine mapBifunctor.hom_ext_of_map F (fun i₁ i₂ h ↦ ?_)
  have hτ : δ F (K.X i₁) (L.X i₂) ≫ (τ.app (K.X i₁) ⊗ₘ τ.app (L.X i₂)) =
      τ.app _ ≫ δ F' (K.X i₁) (L.X i₂) := by
    rw [← cancel_epi (μ F (K.X i₁) (L.X i₂)), Monoidal.μ_δ_assoc,
      NatTrans.IsMonoidal.tensor_assoc, Monoidal.μ_δ, Category.comp_id]
  rw [comp_f, comp_f, NatTrans.mapHomologicalComplex_app_f]
  have hn := τ.naturality (ιMapBifunctor K L (curriedTensor C) (.up ℤ) i₁ i₂ n h)
  erw [reassoc_of% hn, map_ιMapBifunctor_mapBifunctorComparisonX,
    map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  erw [ι_mapBifunctorMap]
  simp only [mapBifunctorComparisonApp, OplaxMonoidal.δNatTrans_app_app]
  erw [← reassoc_of% hτ]
  simp [tensorHom_def]

end ComplexLevel

section Compatibility

open OplaxMonoidal LaxMonoidal

variable {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
  [HasFunctorialFlatResolution E]

omit [HasFunctorialFlatResolution C] [HasFunctorialFlatResolution D] in
open HomotopyCategory in
/-- A monoidal natural transformation `τ : F ⟶ F'` commutes with the comonoidal comparisons
in the homotopy category. -/
lemma mapHomotopyCategoryδNatTrans_naturality {F F' : C ⥤ D} [F.Additive] [F'.Additive]
    [F.IsLeftAdjoint] [F'.IsLeftAdjoint] [F.Monoidal] [F'.Monoidal] (τ : F ⟶ F')
    [NatTrans.IsMonoidal τ] (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    (NatTrans.mapHomotopyCategory τ (.up ℤ)).app (X₁ ⊗ X₂) ≫
        ((mapHomotopyCategoryδNatTrans (.up ℤ) F').app X₁).app X₂ =
      ((mapHomotopyCategoryδNatTrans (.up ℤ) F).app X₁).app X₂ ≫
        ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app X₁ ⊗ₘ
          (NatTrans.mapHomotopyCategory τ (.up ℤ)).app X₂) := by
  obtain ⟨K, rfl⟩ := quotient_obj_surjective X₁
  obtain ⟨L, rfl⟩ := quotient_obj_surjective X₂
  have h := (quotient D (.up ℤ)).congr_map (mapHomologicalComplexδNatTrans_naturality τ K L)
  have hq : (quotient D (.up ℤ)).map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K ⊗ₘ
      (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L) =
      (quotient D (.up ℤ)).map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) ⊗ₘ
        (quotient D (.up ℤ)).map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app L) := by
    rw [Functor.Monoidal.map_tensor]
    exact (Category.id_comp _).trans (Category.comp_id _)
  rw [Functor.map_comp, Functor.map_comp, hq] at h
  rw [mapHomotopyCategoryδNatTrans_app_app, mapHomotopyCategoryδNatTrans_app_app]
  exact h

omit [HasFunctorialFlatResolution C] [HasFunctorialFlatResolution D]
  [HasFunctorialFlatResolution E] in
open HomotopyCategory in
/-- The comonoidal comparison of `F ⋙ G` in the homotopy category is the comparison of `F`
followed by the comparison of `G`. -/
lemma mapHomotopyCategoryδNatTrans_comp (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] [F.OplaxMonoidal] [G.OplaxMonoidal]
    (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    ((mapHomotopyCategoryδNatTrans (.up ℤ) (F ⋙ G)).app X₁).app X₂ =
      (G.mapHomotopyCategory _).map (((mapHomotopyCategoryδNatTrans (.up ℤ) F).app X₁).app X₂) ≫
        ((mapHomotopyCategoryδNatTrans (.up ℤ) G).app
          ((F.mapHomotopyCategory _).obj X₁)).app ((F.mapHomotopyCategory _).obj X₂) := by
  obtain ⟨K, rfl⟩ := quotient_obj_surjective X₁
  obtain ⟨L, rfl⟩ := quotient_obj_surjective X₂
  rw [mapHomotopyCategoryδNatTrans_app_app, mapHomotopyCategoryδNatTrans_app_app,
    mapHomotopyCategory_map]
  erw [mapHomotopyCategoryδNatTrans_app_app]
  rw [← Functor.map_comp, mapHomologicalComplexδNatTrans_comp]
  rfl

end Compatibility

section Derived

open OplaxMonoidal LaxMonoidal

variable {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
  [HasFunctorialFlatResolution E]

section

variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]

/-- The component of `derivedTensorLeftDerivedCounit F` at `(X₁, X₂)` is the tensor product of
the counits of `LF`, followed by the lax monoidal structure of `Qh`. -/
lemma derivedTensorLeftDerivedCounit_app_app (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    ((derivedTensorLeftDerivedCounit F).app X₁).app X₂ =
      (F.leftDerivedFunctorCounit.app X₁ ⊗ₘ F.leftDerivedFunctorCounit.app X₂) ≫
        μ Qh ((F.mapHomotopyCategory _).obj X₁) ((F.mapHomotopyCategory _).obj X₂) := by
  simp [derivedTensorLeftDerivedCounit, tensorHom_def]

omit [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D] in
/-- The component of `leftDerivedDerivedTensorCounit F` at `(X₁, X₂)` is `LF` applied to the
lax monoidal structure of `Qh`, followed by the counit of `LF` at `X₁ ⊗ X₂`. -/
lemma leftDerivedDerivedTensorCounit_app_app (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    ((leftDerivedDerivedTensorCounit F).app X₁).app X₂ =
      F.leftDerivedFunctor.map (μ Qh X₁ X₂) ≫ F.leftDerivedFunctorCounit.app (X₁ ⊗ X₂) := by
  simp [leftDerivedDerivedTensorCounit]

variable [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

/-- The characterising property of `leftDerivedTensorComparison`, with tensor products of
morphisms. -/
@[reassoc]
lemma leftDerivedTensorComparison_app_app_comp_tensorHom (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    ((F.leftDerivedTensorComparison.app (Qh.obj X₁)).app (Qh.obj X₂)) ≫
        (F.leftDerivedFunctorCounit.app X₁ ⊗ₘ F.leftDerivedFunctorCounit.app X₂) ≫
        μ Qh ((F.mapHomotopyCategory _).obj X₁) ((F.mapHomotopyCategory _).obj X₂) =
      F.leftDerivedFunctor.map (μ Qh X₁ X₂) ≫ F.leftDerivedFunctorCounit.app (X₁ ⊗ X₂) ≫
        Qh.map (((mapHomotopyCategoryδNatTrans (.up ℤ) F).app X₁).app X₂) := by
  have := F.leftDerivedTensorComparison_app_app_comp_counit X₁ X₂
  rw [derivedTensorLeftDerivedCounit_app_app, leftDerivedDerivedTensorCounit_app_app] at this
  simpa using this

end

section NatIso

variable {F F' : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [F'.PreservesFlat] [F'.IsLeftAdjoint] [F'.Monoidal]

/-- A monoidal natural isomorphism `τ : F ≅ F'` carries the tensor comparison of `LF` to the
one of `LF'`, as natural transformations of bifunctors. -/
lemma leftDerivedTensorComparison_naturality (τ : F ≅ F') [NatTrans.IsMonoidal τ.hom] :
    (postcompose₂.map (F.leftDerivedFunctorNatIso τ).hom).app (curriedTensor _) ≫
        F'.leftDerivedTensorComparison =
      F.leftDerivedTensorComparison ≫
        (((whiskeringLeft₂ _).map (F.leftDerivedFunctorNatIso τ).hom).app
          F.leftDerivedFunctor).app (curriedTensor _) ≫
        (((whiskeringLeft₂ _).obj F'.leftDerivedFunctor).map
          (F.leftDerivedFunctorNatIso τ).hom).app (curriedTensor _) := by
  apply leftDerived₂_ext (derivedTensorLeftDerived F') (derivedTensorLeftDerivedCounit F')
    (HomotopyCategory.quasiIso _ _) (HomotopyCategory.quasiIso _ _)
  ext X₁ X₂
  dsimp
  simp only [Category.assoc]
  rw [derivedTensorLeftDerivedCounit_app_app, leftDerivedTensorComparison_app_app_comp_tensorHom,
    ← tensorHom_def_assoc, tensorHom_comp_tensorHom_assoc,
    leftDerivedFunctorNatIso_hom_app_comp_counit, leftDerivedFunctorNatIso_hom_app_comp_counit,
    ← tensorHom_comp_tensorHom_assoc, μ_natural,
    leftDerivedTensorComparison_app_app_comp_tensorHom_assoc,
    ← Qh.map_comp, ← mapHomotopyCategoryδNatTrans_naturality, Qh.map_comp,
    ← leftDerivedFunctorNatIso_hom_app_comp_counit_assoc]
  erw [← NatTrans.naturality_assoc]

/-- The componentwise form of `CategoryTheory.Functor.leftDerivedTensorComparison_naturality`:
a monoidal natural isomorphism `τ : F ≅ F'` carries the tensor comparison of `LF` at `(K, M)` to
the one of `LF'`. -/
@[reassoc]
lemma leftDerivedTensorComparison_naturality_app (τ : F ≅ F') [NatTrans.IsMonoidal τ.hom]
    (K M : DerivedCategory C) :
    (F.leftDerivedFunctorNatIso τ).hom.app (K ⊗ M) ≫
        (F'.leftDerivedTensorComparison.app K).app M =
      (F.leftDerivedTensorComparison.app K).app M ≫
        ((F.leftDerivedFunctorNatIso τ).hom.app K ⊗ₘ (F.leftDerivedFunctorNatIso τ).hom.app M) := by
  have h := congr_app (congr_app (leftDerivedTensorComparison_naturality τ) K) M
  dsimp at h
  rw [h, tensorHom_def]

end NatIso

section Comp

instance preservesFlat_comp (F : C ⥤ D) (G : D ⥤ E) [F.PreservesFlat] [G.PreservesFlat] :
    (F ⋙ G).PreservesFlat :=
  ⟨fun hX ↦ PreservesFlat.flat_obj (F := G) (PreservesFlat.flat_obj (F := F) hX)⟩

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]

/-- The naturality of the tensor comparison of `LF`, with tensor products of morphisms. -/
@[reassoc]
lemma leftDerivedTensorComparison_naturality_tensorHom {K₁ K₂ M₁ M₂ : DerivedCategory C}
    (f : K₁ ⟶ K₂) (g : M₁ ⟶ M₂) :
    F.leftDerivedFunctor.map (f ⊗ₘ g) ≫ (F.leftDerivedTensorComparison.app K₂).app M₂ =
      (F.leftDerivedTensorComparison.app K₁).app M₁ ≫
        (F.leftDerivedFunctor.map f ⊗ₘ F.leftDerivedFunctor.map g) := by
  have h₁ := congr_app (F.leftDerivedTensorComparison.naturality f) M₁
  have h₂ := (F.leftDerivedTensorComparison.app K₂).naturality g
  dsimp at h₁ h₂
  rw [tensorHom_def, Functor.map_comp, Category.assoc, h₂, reassoc_of% h₁, tensorHom_def]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The tensor comparison of `L(F ⋙ G)` is, through `L(F ⋙ G) ≅ LF ⋙ LG`, the tensor
comparison of `LF` followed by the tensor comparison of `LG`, as natural transformations of
bifunctors. -/
lemma leftDerivedTensorComparison_comp :
    (F ⋙ G).leftDerivedTensorComparison =
      (postcompose₂.map (F.leftDerivedFunctorCompIso G).hom).app (curriedTensor _) ≫
        (postcompose₂.obj G.leftDerivedFunctor).map F.leftDerivedTensorComparison ≫
        (((whiskeringLeft₂ _).obj F.leftDerivedFunctor).obj F.leftDerivedFunctor).map
          G.leftDerivedTensorComparison ≫
        (((whiskeringLeft₂ _).map (F.leftDerivedFunctorCompIso G).inv).app
          (F.leftDerivedFunctor ⋙ G.leftDerivedFunctor)).app (curriedTensor _) ≫
        (((whiskeringLeft₂ _).obj (F ⋙ G).leftDerivedFunctor).map
          (F.leftDerivedFunctorCompIso G).inv).app (curriedTensor _) := by
  apply leftDerived₂_ext (derivedTensorLeftDerived (F ⋙ G))
    (derivedTensorLeftDerivedCounit (F ⋙ G))
    (HomotopyCategory.quasiIso _ _) (HomotopyCategory.quasiIso _ _)
  ext X₁ X₂
  dsimp
  simp only [Category.assoc]
  have k (X : HomotopyCategory C (.up ℤ)) :
      (F.leftDerivedFunctorCompIso G).inv.app (Qh.obj X) ≫
          (F ⋙ G).leftDerivedFunctorCounit.app X =
        G.leftDerivedFunctor.map (F.leftDerivedFunctorCounit.app X) ≫
          G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory _).obj X) := by
    rw [← leftDerivedFunctorCompIso_hom_app_comp_counit, Iso.inv_hom_id_app_assoc]
  rw [derivedTensorLeftDerivedCounit_app_app, leftDerivedTensorComparison_app_app_comp_tensorHom,
    ← tensorHom_def_assoc, tensorHom_comp_tensorHom_assoc, k, k,
    ← tensorHom_comp_tensorHom_assoc]
  have n := leftDerivedTensorComparison_naturality_tensorHom G
    (F.leftDerivedFunctorCounit.app X₁) (F.leftDerivedFunctorCounit.app X₂)
  have c := leftDerivedTensorComparison_app_app_comp_tensorHom G
    ((F.mapHomotopyCategory _).obj X₁) ((F.mapHomotopyCategory _).obj X₂)
  rw [← reassoc_of% n]
  erw [c]
  have cF := leftDerivedTensorComparison_app_app_comp_tensorHom F X₁ X₂
  have nG := G.leftDerivedFunctorCounit.naturality
    (X := (F.mapHomotopyCategory _).obj (X₁ ⊗ X₂))
    (Y := (F.mapHomotopyCategory _).obj X₁ ⊗ (F.mapHomotopyCategory _).obj X₂)
    (((mapHomotopyCategoryδNatTrans (.up ℤ) F).app X₁).app X₂)
  have ne := (F.leftDerivedFunctorCompIso G).hom.naturality (μ Qh X₁ X₂)
  dsimp only [Functor.comp_obj, Functor.comp_map] at nG ne
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, cF,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, reassoc_of% nG,
    ← reassoc_of% ne, leftDerivedFunctorCompIso_hom_app_comp_counit_assoc,
    mapHomotopyCategoryδNatTrans_comp, Qh.map_comp]

/-- The componentwise form of `CategoryTheory.Functor.leftDerivedTensorComparison_comp`: the
tensor comparison of `LF` followed by the one of `LG` is the tensor comparison of `L(F ⋙ G)`,
through `L(F ⋙ G) ≅ LF ⋙ LG`. -/
@[reassoc]
lemma map_leftDerivedTensorComparison_app_app_comp (K M : DerivedCategory C) :
    G.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app K).app M) ≫
        (G.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj K)).app
          (F.leftDerivedFunctor.obj M) =
      (F.leftDerivedFunctorCompIso G).inv.app (K ⊗ M) ≫
        ((F ⋙ G).leftDerivedTensorComparison.app K).app M ≫
        ((F.leftDerivedFunctorCompIso G).hom.app K ⊗ₘ
          (F.leftDerivedFunctorCompIso G).hom.app M) := by
  have h := congr_app (congr_app (leftDerivedTensorComparison_comp F G) K) M
  dsimp at h
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← tensorHom_def_assoc, tensorHom_comp_tensorHom]
  simp

end Comp

section Square

variable {D' : Type u₄} [Category.{u + 1} D'] [Abelian D'] [IsGrothendieckAbelian.{u + 1} D']
  [MonoidalCategory D'] [MonoidalPreadditive D'] [MonoidalClosed D'] [BraidedCategory D']
  [HasFunctorialFlatResolution D']
  (F₁ : C ⥤ D) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₁.PreservesFlat] [F₁.IsLeftAdjoint] [F₁.Monoidal]
  (F₂ : D ⥤ E) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [F₂.PreservesFlat] [F₂.IsLeftAdjoint] [F₂.Monoidal]
  (G₁ : C ⥤ D') [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₁.PreservesFlat] [G₁.IsLeftAdjoint] [G₁.Monoidal]
  (G₂ : D' ⥤ E) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [G₂.PreservesFlat] [G₂.IsLeftAdjoint] [G₂.Monoidal]

/-- The isomorphism `LG₁ ⋙ LG₂ ≅ LF₁ ⋙ LF₂` of left derived functors induced by an
isomorphism `τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂` of exact functors. -/
noncomputable def leftDerivedFunctorCompNatIso (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) :
    G₁.leftDerivedFunctor ⋙ G₂.leftDerivedFunctor ≅
      F₁.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor :=
  (G₁.leftDerivedFunctorCompIso G₂).symm ≪≫ (G₁ ⋙ G₂).leftDerivedFunctorNatIso τ ≪≫
    F₁.leftDerivedFunctorCompIso F₂

/-- A monoidal isomorphism `τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂` of exact functors identifies the composite
of the tensor comparisons of `LF₁` and `LF₂` with the composite of those of `LG₁` and `LG₂`,
through the induced isomorphism `α : LG₁ ⋙ LG₂ ≅ LF₁ ⋙ LF₂`:
```
LF₂(LF₁(K ⊗ᴸ M)) ⟶ LF₂(LF₁K ⊗ᴸ LF₁M) ⟶ LF₂LF₁K ⊗ᴸ LF₂LF₁M
```
is `α⁻¹` followed by the corresponding composite for `G₁, G₂` and by `α ⊗ α`. -/
lemma map_leftDerivedTensorComparison_comp_eq_of_iso (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    [NatTrans.IsMonoidal τ.hom] (K M : DerivedCategory C) :
    F₂.leftDerivedFunctor.map ((F₁.leftDerivedTensorComparison.app K).app M) ≫
        (F₂.leftDerivedTensorComparison.app (F₁.leftDerivedFunctor.obj K)).app
          (F₁.leftDerivedFunctor.obj M) =
      (leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).inv.app (K ⊗ M) ≫
        G₂.leftDerivedFunctor.map ((G₁.leftDerivedTensorComparison.app K).app M) ≫
        (G₂.leftDerivedTensorComparison.app (G₁.leftDerivedFunctor.obj K)).app
          (G₁.leftDerivedFunctor.obj M) ≫
        ((leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).hom.app K ⊗ₘ
          (leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).hom.app M) := by
  rw [map_leftDerivedTensorComparison_app_app_comp,
    map_leftDerivedTensorComparison_app_app_comp_assoc]
  simp only [leftDerivedFunctorCompNatIso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  congr 1
  rw [← cancel_epi (((G₁ ⋙ G₂).leftDerivedFunctorNatIso τ).hom.app _),
    Iso.hom_inv_id_app_assoc, leftDerivedTensorComparison_naturality_app_assoc,
    tensorHom_comp_tensorHom]
  simp

end Square

end Derived

end CategoryTheory.Functor
