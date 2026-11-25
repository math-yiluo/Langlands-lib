/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.TensorIso

/-!
# The derived tensor comparison of a functor commuting with tensor products

Let `F : C ⥤ D` be an exact functor between monoidal Grothendieck abelian categories with
functorial flat resolutions, which preserves flat objects and is a left adjoint, and let
`δ : F(A ⊗ B) ⟶ F A ⊗ F B` be a natural transformation of bifunctors, with no compatibility with
the associators or unitors (`CategoryTheory.Functor.TensorComparison F`). As for the comonoidal
structure of an oplax monoidal functor (`CategoryTheory.Functor.leftDerivedTensorComparison`),
`δ` derives to a natural transformation `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M`
(`CategoryTheory.Functor.leftDerivedTensorComparisonOfNatTrans`), an isomorphism if `δ` is one.
For a strong monoidal `F` and `δ` its comonoidal structure, this is
`CategoryTheory.Functor.leftDerivedTensorComparison` (by definition).

This applies to equivalences of categories which commute with the tensor products without being
known to be monoidal. We show that these comparisons are compatible with composition and with
natural isomorphisms commuting with the `δ`'s, and deduce the compatibility of the comparisons
with the isomorphisms `LG₁ ⋙ LG₂ ≅ LF₁ ⋙ LF₂` induced by isomorphisms `G₁ ⋙ G₂ ≅ F₁ ⋙ F₂`
commuting with the `δ`'s
(`CategoryTheory.Functor.comparisonCompatible_leftDerivedFunctorCompNatIso_of_tensorComparison`).

Finally, `CategoryTheory.Adjunction.ComparisonCompatible.ofIso` transports the compatibility
condition `CategoryTheory.Adjunction.ComparisonCompatible` along isomorphisms of the functors
carrying the tensor isomorphisms.
-/

@[expose] public section

universe u u₁ u₂ u₃ u₄

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

section General

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalCategory E]

/-- A comparison `F (X ⊗ Y) ⟶ F X ⊗ F Y` for a functor `F` between monoidal categories: a natural
transformation of bifunctors, with no coherence condition. -/
abbrev TensorComparison (F : C ⥤ D) : Type _ :=
  (postcompose₂.obj F).obj (curriedTensor C) ⟶
    (((whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D)

/-- The comparison of a composite `F ⋙ G`: `G (F (X ⊗ Y)) ⟶ G (F X ⊗ F Y) ⟶ G (F X) ⊗ G (F Y)`. -/
noncomputable def TensorComparison.comp {F : C ⥤ D} (δF : F.TensorComparison) {G : D ⥤ E}
    (δG : G.TensorComparison) : (F ⋙ G).TensorComparison :=
  (postcompose₂.obj G).map δF ≫ (((whiskeringLeft₂ E).obj F).obj F).map δG

@[simp]
lemma TensorComparison.comp_app_app {F : C ⥤ D} (δF : F.TensorComparison) {G : D ⥤ E}
    (δG : G.TensorComparison) (X Y : C) :
    ((δF.comp δG).app X).app Y =
      G.map ((δF.app X).app Y) ≫ (δG.app (F.obj X)).app (F.obj Y) :=
  rfl

/-- A natural transformation `τ : F ⟶ G` is compatible with comparisons `δF` and `δG` if
`τ (X ⊗ Y) ≫ δG X Y = δF X Y ≫ (τ X ⊗ τ Y)` for all `X` and `Y`. -/
def _root_.CategoryTheory.NatTrans.TensorCompatible {F G : C ⥤ D} (τ : F ⟶ G)
    (δF : F.TensorComparison) (δG : G.TensorComparison) : Prop :=
  ∀ X Y : C, τ.app (X ⊗ Y) ≫ (δG.app X).app Y = (δF.app X).app Y ≫ (τ.app X ⊗ₘ τ.app Y)

/-- If an isomorphism is compatible with comparisons, so is its inverse. -/
lemma _root_.CategoryTheory.NatTrans.TensorCompatible.inv {F G : C ⥤ D} {τ : F ≅ G}
    {δF : F.TensorComparison} {δG : G.TensorComparison}
    (h : NatTrans.TensorCompatible τ.hom δF δG) : NatTrans.TensorCompatible τ.inv δG δF :=
  fun X Y ↦ by
    rw [← cancel_epi (τ.hom.app (X ⊗ Y)), Iso.hom_inv_id_app_assoc, reassoc_of% (h X Y),
      tensorHom_comp_tensorHom]
    simp

end General

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]

section ComplexLevel

open HomologicalComplex HomotopyCategory

variable (F : C ⥤ D) [F.Additive] [F.IsLeftAdjoint] (δ : F.TensorComparison)

/-- The comparison `F(K ⊗ L) ⟶ F(K) ⊗ F(L)` in the homotopy category induced by a comparison
`δ : F (X ⊗ Y) ⟶ F X ⊗ F Y`: the comparison `HomologicalComplex.mapBifunctorComparisonNatTrans`
of complexes, passed to the quotient. For the comonoidal structure of an oplax monoidal functor,
this is `CategoryTheory.Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans`. -/
noncomputable def mapHomotopyCategoryTensorComparison :
    (postcompose₂.obj (F.mapHomotopyCategory (.up ℤ))).obj
        (curriedTensor (HomotopyCategory C (.up ℤ))) ⟶
      (((whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
        (F.mapHomotopyCategory (.up ℤ))).obj (curriedTensor (HomotopyCategory D (.up ℤ))) :=
  Quotient.natTransLift₂' _ _
    ((postcompose₂.obj (HomotopyCategory.quotient D (.up ℤ))).map
      (mapBifunctorComparisonNatTrans δ (.up ℤ)))

@[simp]
lemma mapHomotopyCategoryTensorComparison_app_app (K L : CochainComplex C ℤ) :
    ((F.mapHomotopyCategoryTensorComparison δ).app ((quotient C (.up ℤ)).obj K)).app
        ((quotient C (.up ℤ)).obj L) =
      (quotient D (.up ℤ)).map (mapBifunctorComparison δ (.up ℤ) K L) :=
  rfl

/-- For an oplax monoidal functor, the comparison induced by the comonoidal structure is
`OplaxMonoidal.mapHomotopyCategoryδNatTrans`. -/
lemma mapHomotopyCategoryTensorComparison_δNatTrans [F.OplaxMonoidal] :
    F.mapHomotopyCategoryTensorComparison (OplaxMonoidal.δNatTrans F) =
      OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F :=
  rfl


instance [IsIso δ] : IsIso (F.mapHomotopyCategoryTensorComparison δ) := by
  have (X Y : C) : IsIso ((δ.app X).app Y) := inferInstance
  have (K L : CochainComplex C ℤ) : IsIso ((((postcompose₂.obj
      (HomotopyCategory.quotient D (.up ℤ))).map (mapBifunctorComparisonNatTrans δ (.up ℤ))).app
        K).app L) :=
    Functor.map_isIso (HomotopyCategory.quotient D (.up ℤ)) (mapBifunctorComparison δ (.up ℤ) K L)
  exact Quotient.isIso_natTransLift₂ _ _ _

/-- A natural transformation `τ : F ⟶ F'` commuting with comparisons `δ` and `δ'` commutes with
the induced comparisons of complexes. -/
lemma mapBifunctorComparison_naturality_of_tensorComparison {F F' : C ⥤ D} [F.Additive]
    [F'.Additive] [F.IsLeftAdjoint] [F'.IsLeftAdjoint] (δ : F.TensorComparison)
    (δ' : F'.TensorComparison) (τ : F ⟶ F')
    (hτ : NatTrans.TensorCompatible τ δ δ')
    (K L : CochainComplex C ℤ) :
    (NatTrans.mapHomologicalComplex τ (.up ℤ)).app (K ⊗ L) ≫
        ((mapBifunctorComparisonNatTrans δ' (.up ℤ)).app K).app L =
      ((mapBifunctorComparisonNatTrans δ (.up ℤ)).app K).app L ≫
        ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K ⊗ₘ
          (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L) := by
  ext n
  refine mapBifunctor.hom_ext_of_map F (fun i₁ i₂ h ↦ ?_)
  rw [comp_f, comp_f, NatTrans.mapHomologicalComplex_app_f]
  have hn := τ.naturality (ιMapBifunctor K L (curriedTensor C) (.up ℤ) i₁ i₂ n h)
  erw [reassoc_of% hn, map_ιMapBifunctor_mapBifunctorComparisonX,
    map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  erw [ι_mapBifunctorMap]
  simp only [mapBifunctorComparisonApp]
  erw [reassoc_of% (hτ (K.X i₁) (L.X i₂))]
  simp [tensorHom_def]

omit [MonoidalClosed C] [BraidedCategory C] [MonoidalClosed D] [BraidedCategory D]
  [MonoidalClosed E] [BraidedCategory E] in
/-- The comparison of complexes induced by the comparison `δF.comp δG` of `F ⋙ G` is the
comparison of `F` followed by the comparison of `G`. -/
lemma mapBifunctorComparison_comp_tensorComparison (F : C ⥤ D) (G : D ⥤ E) [F.Additive]
    [G.Additive] [F.IsLeftAdjoint] [G.IsLeftAdjoint] (δF : F.TensorComparison)
    (δG : G.TensorComparison) (K L : CochainComplex C ℤ) :
    ((mapBifunctorComparisonNatTrans (δF.comp δG) (.up ℤ)).app K).app L =
      (G.mapHomologicalComplex _).map (((mapBifunctorComparisonNatTrans δF (.up ℤ)).app K).app L) ≫
        ((mapBifunctorComparisonNatTrans δG (.up ℤ)).app
          ((F.mapHomologicalComplex _).obj K)).app ((F.mapHomologicalComplex _).obj L) := by
  ext n
  refine mapBifunctor.hom_ext_of_map (F ⋙ G) (fun i₁ i₂ h ↦ ?_)
  simp only [mapBifunctorComparisonNatTrans_app_app, mapBifunctorComparison_f,
    comp_f, Functor.mapHomologicalComplex_map_f, map_ιMapBifunctor_mapBifunctorComparisonX]
  erw [Functor.comp_map, ← G.map_comp_assoc, map_ιMapBifunctor_mapBifunctorComparisonX,
    G.map_comp_assoc, map_ιMapBifunctor_mapBifunctorComparisonX]
  simp
  rfl

end ComplexLevel

section Compatibility

open HomotopyCategory

/-- A natural transformation `τ : F ⟶ F'` commuting with comparisons `δ` and `δ'` commutes with
the induced comparisons in the homotopy category. -/
lemma mapHomotopyCategoryTensorComparison_naturality {F F' : C ⥤ D} [F.Additive]
    [F'.Additive] [F.IsLeftAdjoint] [F'.IsLeftAdjoint] (δ : F.TensorComparison)
    (δ' : F'.TensorComparison) (τ : F ⟶ F')
    (hτ : NatTrans.TensorCompatible τ δ δ')
    (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    (NatTrans.mapHomotopyCategory τ (.up ℤ)).app (X₁ ⊗ X₂) ≫
        ((F'.mapHomotopyCategoryTensorComparison δ').app X₁).app X₂ =
      ((F.mapHomotopyCategoryTensorComparison δ).app X₁).app X₂ ≫
        ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app X₁ ⊗ₘ
          (NatTrans.mapHomotopyCategory τ (.up ℤ)).app X₂) := by
  obtain ⟨K, rfl⟩ := quotient_obj_surjective X₁
  obtain ⟨L, rfl⟩ := quotient_obj_surjective X₂
  have h := (quotient D (.up ℤ)).congr_map
    (mapBifunctorComparison_naturality_of_tensorComparison δ δ' τ hτ K L)
  have hq : (quotient D (.up ℤ)).map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K ⊗ₘ
      (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L) =
      (quotient D (.up ℤ)).map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) ⊗ₘ
        (quotient D (.up ℤ)).map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app L) := by
    rw [Functor.Monoidal.map_tensor]
    exact (Category.id_comp _).trans (Category.comp_id _)
  rw [Functor.map_comp, Functor.map_comp, hq] at h
  rw [mapHomotopyCategoryTensorComparison_app_app, mapHomotopyCategoryTensorComparison_app_app]
  exact h

/-- The comparison in the homotopy category induced by `δF.comp δG` is the comparison of `F`
followed by the comparison of `G`. -/
lemma mapHomotopyCategoryTensorComparison_comp (F : C ⥤ D) (G : D ⥤ E) [F.Additive]
    [G.Additive] [F.IsLeftAdjoint] [G.IsLeftAdjoint] (δF : F.TensorComparison)
    (δG : G.TensorComparison) (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    (((F ⋙ G).mapHomotopyCategoryTensorComparison (δF.comp δG)).app X₁).app X₂ =
      (G.mapHomotopyCategory _).map (((F.mapHomotopyCategoryTensorComparison δF).app X₁).app X₂) ≫
        ((G.mapHomotopyCategoryTensorComparison δG).app
          ((F.mapHomotopyCategory _).obj X₁)).app ((F.mapHomotopyCategory _).obj X₂) := by
  obtain ⟨K, rfl⟩ := quotient_obj_surjective X₁
  obtain ⟨L, rfl⟩ := quotient_obj_surjective X₂
  rw [mapHomotopyCategoryTensorComparison_app_app, mapHomotopyCategoryTensorComparison_app_app,
    mapHomotopyCategory_map]
  erw [mapHomotopyCategoryTensorComparison_app_app]
  rw [← Functor.map_comp]
  erw [← mapBifunctorComparison_comp_tensorComparison]
  rfl

end Compatibility

section Derived

variable [HasFunctorialFlatResolution C] [HasFunctorialFlatResolution D]
  [HasFunctorialFlatResolution E]

open OplaxMonoidal LaxMonoidal

section Comparison

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] (δ : F.TensorComparison)

/-- The comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` of bifunctors `D(C) ⥤ D(C) ⥤ D(D)` obtained by
deriving a comparison `δ : F (X ⊗ Y) ⟶ F X ⊗ F Y`. It is the unique natural transformation such
that, for `K, M` in `K(C)`, the square
```
  LF(Qh K ⊗ᴸ Qh M) ──comparison──▶ LF(Qh K) ⊗ᴸ LF(Qh M)
          │                                │
          ▼                                ▼
     Qh(F(K ⊗ M)) ────────Qh(δ)───────▶ Qh(F K ⊗ F M)
```
commutes, the vertical arrows being `leftDerivedDerivedTensorCounit` and
`derivedTensorLeftDerivedCounit`. -/
noncomputable def leftDerivedTensorComparisonOfNatTrans :
    leftDerivedDerivedTensor F ⟶ derivedTensorLeftDerived F :=
  leftDerived₂NatTrans _ (derivedTensorLeftDerivedCounit F)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedDerivedTensorCounit F)
    (postcompose₂MapWhiskeringLeft₂ (F.mapHomotopyCategoryTensorComparison δ) Qh)

/-- For a strong monoidal functor, the comparison derived from its comonoidal structure is
`CategoryTheory.Functor.leftDerivedTensorComparison`. -/
lemma leftDerivedTensorComparisonOfNatTrans_δNatTrans [F.Monoidal] :
    F.leftDerivedTensorComparisonOfNatTrans (OplaxMonoidal.δNatTrans F) =
      F.leftDerivedTensorComparison :=
  rfl

/-- The characterising property of `leftDerivedTensorComparisonOfNatTrans`. -/
@[reassoc]
lemma leftDerivedTensorComparisonOfNatTrans_app_app_comp_counit
    (K M : HomotopyCategory C (.up ℤ)) :
    ((F.leftDerivedTensorComparisonOfNatTrans δ).app (Qh.obj K)).app (Qh.obj M) ≫
        ((derivedTensorLeftDerivedCounit F).app K).app M =
      ((leftDerivedDerivedTensorCounit F).app K).app M ≫
        Qh.map (((F.mapHomotopyCategoryTensorComparison δ).app K).app M) :=
  leftDerived₂NatTrans_app_app _ _ _ _ _ _ _ K M

/-- The comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` is an isomorphism if `δ` is one. -/
instance [IsIso δ] : IsIso (F.leftDerivedTensorComparisonOfNatTrans δ) := by
  dsimp only [leftDerivedTensorComparisonOfNatTrans]
  infer_instance

/-- The characterising property of `leftDerivedTensorComparisonOfNatTrans`, with tensor
products of morphisms. -/
@[reassoc]
lemma leftDerivedTensorComparisonOfNatTrans_app_app_comp_tensorHom
    (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    ((F.leftDerivedTensorComparisonOfNatTrans δ).app (Qh.obj X₁)).app (Qh.obj X₂) ≫
        (F.leftDerivedFunctorCounit.app X₁ ⊗ₘ F.leftDerivedFunctorCounit.app X₂) ≫
        μ Qh ((F.mapHomotopyCategory _).obj X₁) ((F.mapHomotopyCategory _).obj X₂) =
      F.leftDerivedFunctor.map (μ Qh X₁ X₂) ≫ F.leftDerivedFunctorCounit.app (X₁ ⊗ X₂) ≫
        Qh.map (((F.mapHomotopyCategoryTensorComparison δ).app X₁).app X₂) := by
  have := F.leftDerivedTensorComparisonOfNatTrans_app_app_comp_counit δ X₁ X₂
  rw [derivedTensorLeftDerivedCounit_app_app, leftDerivedDerivedTensorCounit_app_app] at this
  simpa using this

/-- The naturality of `leftDerivedTensorComparisonOfNatTrans`, with tensor products of
morphisms. -/
@[reassoc]
lemma leftDerivedTensorComparisonOfNatTrans_naturality_tensorHom
    {K₁ K₂ M₁ M₂ : DerivedCategory C} (f : K₁ ⟶ K₂) (g : M₁ ⟶ M₂) :
    F.leftDerivedFunctor.map (f ⊗ₘ g) ≫
        ((F.leftDerivedTensorComparisonOfNatTrans δ).app K₂).app M₂ =
      ((F.leftDerivedTensorComparisonOfNatTrans δ).app K₁).app M₁ ≫
        (F.leftDerivedFunctor.map f ⊗ₘ F.leftDerivedFunctor.map g) := by
  have h₁ := congr_app ((F.leftDerivedTensorComparisonOfNatTrans δ).naturality f) M₁
  have h₂ := ((F.leftDerivedTensorComparisonOfNatTrans δ).app K₂).naturality g
  dsimp at h₁ h₂
  rw [tensorHom_def, Functor.map_comp, Category.assoc, h₂, reassoc_of% h₁, tensorHom_def]

end Comparison

section NatIso

variable {F F' : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint]
  [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [F'.PreservesFlat] [F'.IsLeftAdjoint]

/-- A natural isomorphism `τ : F ≅ F'` commuting with comparisons `δ` and `δ'` carries the
derived comparison of `δ` to the one of `δ'`. -/
@[reassoc]
lemma leftDerivedTensorComparisonOfNatTrans_naturality_app (δ : F.TensorComparison)
    (δ' : F'.TensorComparison) (τ : F ≅ F')
    (hτ : NatTrans.TensorCompatible τ.hom δ δ')
    (K M : DerivedCategory C) :
    (F.leftDerivedFunctorNatIso τ).hom.app (K ⊗ M) ≫
        ((F'.leftDerivedTensorComparisonOfNatTrans δ').app K).app M =
      ((F.leftDerivedTensorComparisonOfNatTrans δ).app K).app M ≫
        ((F.leftDerivedFunctorNatIso τ).hom.app K ⊗ₘ (F.leftDerivedFunctorNatIso τ).hom.app M) := by
  have h : (postcompose₂.map (F.leftDerivedFunctorNatIso τ).hom).app (curriedTensor _) ≫
        F'.leftDerivedTensorComparisonOfNatTrans δ' =
      F.leftDerivedTensorComparisonOfNatTrans δ ≫
        (((whiskeringLeft₂ _).map (F.leftDerivedFunctorNatIso τ).hom).app
          F.leftDerivedFunctor).app (curriedTensor _) ≫
        (((whiskeringLeft₂ _).obj F'.leftDerivedFunctor).map
          (F.leftDerivedFunctorNatIso τ).hom).app (curriedTensor _) := by
    apply leftDerived₂_ext (derivedTensorLeftDerived F') (derivedTensorLeftDerivedCounit F')
      (HomotopyCategory.quasiIso _ _) (HomotopyCategory.quasiIso _ _)
    ext X₁ X₂
    dsimp
    simp only [Category.assoc]
    rw [derivedTensorLeftDerivedCounit_app_app,
      leftDerivedTensorComparisonOfNatTrans_app_app_comp_tensorHom,
      ← tensorHom_def_assoc, tensorHom_comp_tensorHom_assoc,
      leftDerivedFunctorNatIso_hom_app_comp_counit, leftDerivedFunctorNatIso_hom_app_comp_counit,
      ← tensorHom_comp_tensorHom_assoc, μ_natural,
      leftDerivedTensorComparisonOfNatTrans_app_app_comp_tensorHom_assoc,
      ← Qh.map_comp, ← mapHomotopyCategoryTensorComparison_naturality δ δ' τ.hom hτ, Qh.map_comp,
      ← leftDerivedFunctorNatIso_hom_app_comp_counit_assoc]
    erw [← NatTrans.naturality_assoc]
  have h' := congr_app (congr_app h K) M
  dsimp at h'
  rw [h', tensorHom_def]

end NatIso

section Comp

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] (δF : F.TensorComparison)
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.PreservesFlat] [G.IsLeftAdjoint] (δG : G.TensorComparison)

/-- The derived comparison of `δF.comp δG` is, through `L(F ⋙ G) ≅ LF ⋙ LG`, the derived
comparison of `δF` followed by the derived comparison of `δG`. -/
lemma leftDerivedTensorComparisonOfNatTrans_comp :
    (F ⋙ G).leftDerivedTensorComparisonOfNatTrans (δF.comp δG) =
      (postcompose₂.map (F.leftDerivedFunctorCompIso G).hom).app (curriedTensor _) ≫
        (postcompose₂.obj G.leftDerivedFunctor).map
          (F.leftDerivedTensorComparisonOfNatTrans δF) ≫
        (((whiskeringLeft₂ _).obj F.leftDerivedFunctor).obj F.leftDerivedFunctor).map
          (G.leftDerivedTensorComparisonOfNatTrans δG) ≫
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
  rw [derivedTensorLeftDerivedCounit_app_app,
    leftDerivedTensorComparisonOfNatTrans_app_app_comp_tensorHom,
    ← tensorHom_def_assoc, tensorHom_comp_tensorHom_assoc, k, k,
    ← tensorHom_comp_tensorHom_assoc]
  have n := leftDerivedTensorComparisonOfNatTrans_naturality_tensorHom G δG
    (F.leftDerivedFunctorCounit.app X₁) (F.leftDerivedFunctorCounit.app X₂)
  have c := leftDerivedTensorComparisonOfNatTrans_app_app_comp_tensorHom G δG
    ((F.mapHomotopyCategory _).obj X₁) ((F.mapHomotopyCategory _).obj X₂)
  rw [← reassoc_of% n]
  erw [c]
  have cF := leftDerivedTensorComparisonOfNatTrans_app_app_comp_tensorHom F δF X₁ X₂
  have nG := G.leftDerivedFunctorCounit.naturality
    (X := (F.mapHomotopyCategory _).obj (X₁ ⊗ X₂))
    (Y := (F.mapHomotopyCategory _).obj X₁ ⊗ (F.mapHomotopyCategory _).obj X₂)
    (((F.mapHomotopyCategoryTensorComparison δF).app X₁).app X₂)
  have ne := (F.leftDerivedFunctorCompIso G).hom.naturality (μ Qh X₁ X₂)
  dsimp only [Functor.comp_obj, Functor.comp_map] at nG ne
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, cF,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, reassoc_of% nG,
    ← reassoc_of% ne, leftDerivedFunctorCompIso_hom_app_comp_counit_assoc,
    mapHomotopyCategoryTensorComparison_comp, Qh.map_comp]

/-- The componentwise form of
`CategoryTheory.Functor.leftDerivedTensorComparisonOfNatTrans_comp`. -/
@[reassoc]
lemma map_leftDerivedTensorComparisonOfNatTrans_app_app_comp (K M : DerivedCategory C) :
    G.leftDerivedFunctor.map (((F.leftDerivedTensorComparisonOfNatTrans δF).app K).app M) ≫
        ((G.leftDerivedTensorComparisonOfNatTrans δG).app (F.leftDerivedFunctor.obj K)).app
          (F.leftDerivedFunctor.obj M) =
      (F.leftDerivedFunctorCompIso G).inv.app (K ⊗ M) ≫
        (((F ⋙ G).leftDerivedTensorComparisonOfNatTrans (δF.comp δG)).app K).app M ≫
        ((F.leftDerivedFunctorCompIso G).hom.app K ⊗ₘ
          (F.leftDerivedFunctorCompIso G).hom.app M) := by
  have h := congr_app (congr_app (leftDerivedTensorComparisonOfNatTrans_comp F δF G δG) K) M
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
  [F₁.PreservesFlat] [F₁.IsLeftAdjoint] (δF₁ : F₁.TensorComparison)
  (F₂ : D ⥤ E) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [F₂.PreservesFlat] [F₂.IsLeftAdjoint] (δF₂ : F₂.TensorComparison)
  (G₁ : C ⥤ D') [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₁.PreservesFlat] [G₁.IsLeftAdjoint] (δG₁ : G₁.TensorComparison)
  (G₂ : D' ⥤ E) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [G₂.PreservesFlat] [G₂.IsLeftAdjoint] (δG₂ : G₂.TensorComparison)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- An isomorphism `τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂` of exact functors commuting with the composite
comparisons identifies the composite of the derived comparisons of `δF₁` and `δF₂` with the
composite of those of `δG₁` and `δG₂`, through the induced isomorphism
`α : LG₁ ⋙ LG₂ ≅ LF₁ ⋙ LF₂`. -/
lemma map_leftDerivedTensorComparisonOfNatTrans_comp_eq_of_iso (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    (hτ : NatTrans.TensorCompatible τ.hom (δG₁.comp δG₂) (δF₁.comp δF₂))
    (K M : DerivedCategory C) :
    F₂.leftDerivedFunctor.map (((F₁.leftDerivedTensorComparisonOfNatTrans δF₁).app K).app M) ≫
        ((F₂.leftDerivedTensorComparisonOfNatTrans δF₂).app (F₁.leftDerivedFunctor.obj K)).app
          (F₁.leftDerivedFunctor.obj M) =
      (leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).inv.app (K ⊗ M) ≫
        G₂.leftDerivedFunctor.map
          (((G₁.leftDerivedTensorComparisonOfNatTrans δG₁).app K).app M) ≫
        ((G₂.leftDerivedTensorComparisonOfNatTrans δG₂).app (G₁.leftDerivedFunctor.obj K)).app
          (G₁.leftDerivedFunctor.obj M) ≫
        ((leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).hom.app K ⊗ₘ
          (leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).hom.app M) := by
  rw [map_leftDerivedTensorComparisonOfNatTrans_app_app_comp,
    map_leftDerivedTensorComparisonOfNatTrans_app_app_comp_assoc]
  simp only [leftDerivedFunctorCompNatIso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  congr 1
  rw [← cancel_epi (((G₁ ⋙ G₂).leftDerivedFunctorNatIso τ).hom.app _),
    Iso.hom_inv_id_app_assoc,
    leftDerivedTensorComparisonOfNatTrans_naturality_app_assoc _ _ τ hτ,
    tensorHom_comp_tensorHom]
  simp

/-- **Derived tensor comparisons along a square**: an isomorphism `τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂` of
exact functors commuting with the composite comparisons induces an isomorphism
`LG₁ ⋙ LG₂ ≅ LF₁ ⋙ LF₂` compatible with the derived comparisons of `δF₁` and `δG₂` and the
derived tensor isomorphisms of `δF₂` and `δG₁`. -/
lemma comparisonCompatible_leftDerivedFunctorCompNatIso_of_tensorComparison [IsIso δF₂]
    [IsIso δG₁] (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    (hτ : NatTrans.TensorCompatible τ.hom (δG₁.comp δG₂) (δF₁.comp δF₂)) :
    Adjunction.ComparisonCompatible (leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ)
      (F₁.leftDerivedTensorComparisonOfNatTrans δF₁)
      (G₂.leftDerivedTensorComparisonOfNatTrans δG₂)
      (asIso (F₂.leftDerivedTensorComparisonOfNatTrans δF₂))
      (asIso (G₁.leftDerivedTensorComparisonOfNatTrans δG₁)) := by
  intro a b
  rw [asIso_hom, asIso_hom,
    map_leftDerivedTensorComparisonOfNatTrans_comp_eq_of_iso _ _ _ _ _ _ _ _ τ hτ,
    tensorHom_def]
  rfl

end Square

end Derived

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

open CategoryTheory.Functor

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
  {F : D ⥤ C} {F' : D' ⥤ C'} {N_D N_D' : D ⥤ D'} {N_C N_C' : C ⥤ C'}
  {α : N_D ⋙ F' ≅ F ⋙ N_C}
  {φ : (postcompose₂.obj F).obj (curriedTensor D) ⟶
    (((whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C)}
  {φ' : (postcompose₂.obj F').obj (curriedTensor D') ⟶
    (((whiskeringLeft₂ C').obj F').obj F').obj (curriedTensor C')}
  {m_C : N_C.TensorIso} {m_D : N_D.TensorIso}

/-- The compatibility `ComparisonCompatible` is transported along isomorphisms `N_C ≅ N_C'` and
`N_D ≅ N_D'` of the functors carrying the tensor isomorphisms. -/
lemma ComparisonCompatible.ofIso (H : ComparisonCompatible α φ φ' m_C m_D) (e_C : N_C ≅ N_C')
    (e_D : N_D ≅ N_D') :
    ComparisonCompatible (isoWhiskerRight e_D.symm F' ≪≫ α ≪≫ isoWhiskerLeft F e_C) φ φ'
      (m_C.ofIso e_C) (m_D.ofIso e_D) := by
  intro a b
  have h := H a b
  have hφ' := congr_app (φ'.naturality (e_D.hom.app a)) (N_D.obj b)
  have hφ'' := (φ'.app (N_D'.obj a)).naturality (e_D.hom.app b)
  have hC := e_C.inv.naturality ((φ.app a).app b)
  have k₁ := TensorIso.ofIso_iso_hom m_C e_C (F.obj a) (F.obj b)
  have k₂ := TensorIso.ofIso_iso_hom m_D e_D a b
  dsimp at h hφ' hφ'' hC k₁ k₂ ⊢
  rw [k₁, k₂, reassoc_of% hC, reassoc_of% h]
  have hφt : F'.map (e_D.hom.app a ⊗ₘ e_D.hom.app b) ≫ (φ'.app (N_D'.obj a)).app (N_D'.obj b) =
      (φ'.app (N_D.obj a)).app (N_D.obj b) ≫
        (F'.map (e_D.hom.app a) ⊗ₘ F'.map (e_D.hom.app b)) := by
    rw [tensorHom_def, F'.map_comp, Category.assoc, hφ'', reassoc_of% hφ', ← tensorHom_def]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% hφt]
  rw [← F'.map_comp_assoc (e_D.hom.app (a ⊗ b)), Iso.hom_inv_id_app, F'.map_id, Category.id_comp,
    ← tensorHom_def, tensorHom_comp_tensorHom]
  simp [tensorHom_def, whisker_exchange_assoc]

end CategoryTheory.Adjunction
