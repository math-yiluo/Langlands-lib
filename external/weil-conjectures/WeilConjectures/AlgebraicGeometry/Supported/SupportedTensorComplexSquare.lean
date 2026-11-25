/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalNatTrans

/-! # Passing coefficient tensor squares to signed total complexes -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
namespace AlgebraicGeometry.Etale

/-- The square of signed total coefficient comparisons, packaged before specialization
so its repeated tensor-complex structures remain shared.
Source: Tag 0F1E (blueprint: lem-pur-supported-tensor-complex-square). -/
@[irreducible]
noncomputable def supportedTensorComplexSquareCondition
    {C D E : Type*} [Category.{w} C] [Category.{w} D] [Category.{w} E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalPreadditive C] [MonoidalPreadditive D] [MonoidalPreadditive E]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    [HasColimitsOfSize.{0, 0} E]
    (G F₁ F₂ : C ⥤ D) (G' F₁' F₂' : C ⥤ E) (H : D ⥤ E)
    [G.Additive] [F₁.Additive] [F₂.Additive]
    [G'.Additive] [F₁'.Additive] [F₂'.Additive] [H.Additive] [H.OplaxMonoidal]
    [PreservesColimitsOfSize.{0, 0} G] [PreservesColimitsOfSize.{0, 0} G']
    [PreservesColimitsOfSize.{0, 0} H]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F₁).obj F₂).obj (curriedTensor D))
    (τ' : (Functor.postcompose₂.obj G').obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ E).obj F₁').obj F₂').obj (curriedTensor E))
    (a₀ : G' ⟶ G ⋙ H) (a₁ : F₁' ⟶ F₁ ⋙ H) (a₂ : F₂' ⟶ F₂ ⋙ H)
    (P Q : CochainComplex C ℤ) : Prop :=
    Functor.mapHomologicalComplexCompNatTrans G H G' a₀ (tensorObj P Q) ≫
      (H.mapHomologicalComplex (.up ℤ)).map (mapBifunctorComparison τ (.up ℤ) P Q) ≫
      mapBifunctorComparison (Functor.OplaxMonoidal.δNatTrans H) (.up ℤ)
        ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
        ((F₂.mapHomologicalComplex (.up ℤ)).obj Q) =
    mapBifunctorComparison τ' (.up ℤ) P Q ≫
      mapBifunctorMap
        (Functor.mapHomologicalComplexCompNatTrans F₁ H F₁' a₁ P)
        (Functor.mapHomologicalComplexCompNatTrans F₂ H F₂' a₂ Q)
        (curriedTensor E) (.up ℤ)

/-- An ordinary coefficient tensor square induces the same square on signed total complexes.
Source: Tag 0F1E, the signed totalization step of supported product localization.
(blueprint: lem-pur-supported-tensor-complex-square).
Proof: in each total degree, use the coproduct extensionality for the image under G' of
all tensor bidegree summands. Naturality of the degreewise coefficient map moves it past
the summand inclusion. The normalization of each total comparison reduces the resulting
square to the assumed ordinary square in that bidegree. Tensoring the two degreewise
maps commutes with the summand inclusions. This proves equality in every degree, hence
equality of the chain maps, with the signed differentials already built into totalization. -/
theorem supportedTensorComplex_square
    {C D E : Type*} [Category.{w} C] [Category.{w} D] [Category.{w} E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalPreadditive C] [MonoidalPreadditive D] [MonoidalPreadditive E]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    [HasColimitsOfSize.{0, 0} E]
    (G F₁ F₂ : C ⥤ D) (G' F₁' F₂' : C ⥤ E) (H : D ⥤ E)
    [G.Additive] [F₁.Additive] [F₂.Additive]
    [G'.Additive] [F₁'.Additive] [F₂'.Additive] [H.Additive] [H.OplaxMonoidal]
    [PreservesColimitsOfSize.{0, 0} G] [PreservesColimitsOfSize.{0, 0} G']
    [PreservesColimitsOfSize.{0, 0} H]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F₁).obj F₂).obj (curriedTensor D))
    (τ' : (Functor.postcompose₂.obj G').obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ E).obj F₁').obj F₂').obj (curriedTensor E))
    (a₀ : G' ⟶ G ⋙ H) (a₁ : F₁' ⟶ F₁ ⋙ H) (a₂ : F₂' ⟶ F₂ ⋙ H)
    (ha : ∀ M N, a₀.app (M ⊗ N) ≫ H.map ((τ.app M).app N) ≫
      Functor.OplaxMonoidal.δ H (F₁.obj M) (F₂.obj N) =
      (τ'.app M).app N ≫ (a₁.app M ⊗ₘ a₂.app N))
    (P Q : CochainComplex C ℤ) :
    supportedTensorComplexSquareCondition G F₁ F₂ G' F₁' F₂' H τ τ' a₀ a₁ a₂ P Q := by
  unfold supportedTensorComplexSquareCondition
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompNatTrans_f,
    Functor.mapHomologicalComplex_map_f]
  apply mapBifunctor.hom_ext_of_map G'
  intro r s hrs
  have hn := a₀.naturality (ιTensorObj P Q r s n hrs)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  erw [← Functor.map_comp_assoc]
  erw [map_ιMapBifunctor_mapBifunctorComparisonX]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [map_ιMapBifunctor_mapBifunctorComparisonX]
  erw [map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  erw [ι_mapBifunctorMap]
  simp only [Functor.mapHomologicalComplexCompNatTrans_f]
  dsimp only [mapBifunctorComparisonApp, Functor.OplaxMonoidal.δNatTrans,
    Functor.mapHomologicalComplex, curriedTensor]
  simpa only [mapBifunctorComparisonApp, Functor.OplaxMonoidal.δNatTrans,
    curriedTensor, tensorHom_def, Category.assoc, Functor.mapHomologicalComplex,
    Functor.comp_obj] using
    congrArg (fun k ↦ k ≫ ιMapBifunctor
      ((H.mapHomologicalComplex (.up ℤ)).obj ((F₁.mapHomologicalComplex (.up ℤ)).obj P))
      ((H.mapHomologicalComplex (.up ℤ)).obj ((F₂.mapHomologicalComplex (.up ℤ)).obj Q))
      (curriedTensor E) (.up ℤ) r s n hrs) (ha (P.X r) (Q.X s))

end AlgebraicGeometry.Etale
