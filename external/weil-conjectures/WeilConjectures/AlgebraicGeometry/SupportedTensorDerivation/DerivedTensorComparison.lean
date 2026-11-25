/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

import WeilConjectures.Mathlib.CategoryTheory.Whiskering

/-! # Descent of a tensor comparison through exact functors -/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.SupportedTensorDerivation

/-- Morphisms comparing a mapped tensor complex with the tensor of two mapped complexes.
Source: blueprint signed total tensor construction
(blueprint: lem-pur-derived-tensor-comparison). -/
noncomputable def ComplexHom
    {C : Type*} [Category.{w} C] {D : Type*} [Category.{w} D]
    [Preadditive C] [Preadditive D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    (P Q : CochainComplex C ℤ) : Type _ :=
  (G.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ⟶
    HomologicalComplex.tensorObj ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
      ((F₂.mapHomologicalComplex (.up ℤ)).obj Q)

/-- The prescribed comparison on each signed tensor bidegree summand.
Source: blueprint signed total tensor construction
(blueprint: lem-pur-derived-tensor-comparison). -/
noncomputable def ComplexCondition
    {C : Type*} [Category.{w} C] {D : Type*} [Category.{w} D]
    [Preadditive C] [Preadditive D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    (θ : ∀ M N : C, G.obj (M ⊗ N) ⟶ F₁.obj M ⊗ F₂.obj N)
    (P Q : CochainComplex C ℤ) (t : ComplexHom G F₁ F₂ P Q) : Prop :=
  ∀ (r s n : ℤ) (h : r + s = n),
    G.map (HomologicalComplex.ιTensorObj P Q r s n h) ≫ t.f n =
      θ (P.X r) (Q.X s) ≫ HomologicalComplex.ιTensorObj
        ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
        ((F₂.mapHomologicalComplex (.up ℤ)).obj Q) r s n h

/-- Extension from the bidegree summands is unique, by the coproduct universal property.
Source: blueprint signed total tensor construction
(blueprint: lem-pur-derived-tensor-comparison). -/
theorem exists_unique_complex
    {D : Type*} [Category.{w} D] {E : Type*} [Category.{w} E]
    [Preadditive D] [Preadditive E] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    (G G₁ G₂ : D ⥤ E) [G.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesColimitsOfSize.{0, 0} G]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ E).obj G₁).obj G₂).obj (curriedTensor E))
    (P Q : CochainComplex D ℤ) :
    ∃! t : ComplexHom G G₁ G₂ P Q,
      ComplexCondition G G₁ G₂ (fun M N ↦ (τ.app M).app N) P Q t := by
  let t := HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P Q
  have ht : ∀ (r s n : ℤ) (h : r + s = n),
      G.map (HomologicalComplex.ιTensorObj P Q r s n h) ≫ t.f n =
        (τ.app (P.X r)).app (Q.X s) ≫ HomologicalComplex.ιTensorObj
          ((G₁.mapHomologicalComplex (.up ℤ)).obj P)
          ((G₂.mapHomologicalComplex (.up ℤ)).obj Q) r s n h := by
    intro r s n h
    exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX τ (.up ℤ) P Q r s n h
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map G
  intro r s h
  exact (ht' r s n h).trans (ht r s n h).symm

section AbstractDerivedTensor

variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type w} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [HasDerivedCategory.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]

section ComplexComparisons

variable (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesColimitsOfSize.{0, 0} G]
  (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ D).obj F₁).obj F₂).obj (curriedTensor D))

/-- The natural comparison of signed total complexes.
Source: blueprint signed total tensor construction
(blueprint: lem-pur-derived-tensor-comparison). -/
noncomputable def ComplexNatTrans :
    (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _) :=
  HomologicalComplex.mapBifunctorComparisonNatTrans τ (.up ℤ)

/-- The component of the comparison of signed total complexes.
Source: blueprint signed total tensor construction
(blueprint: lem-pur-derived-tensor-comparison). -/
noncomputable def ComplexComparison (P Q : CochainComplex C ℤ) :
    ComplexHom G F₁ F₂ P Q :=
  ((ComplexNatTrans G F₁ F₂ τ).app P).app Q

omit [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory D] [Abelian.HasFunctorialFlatResolution D] in
/-- The comparison has the prescribed map on every bidegree summand.
Source: blueprint signed total tensor construction
(blueprint: lem-pur-derived-tensor-comparison). -/
theorem complex_comparison_spec (P Q : CochainComplex C ℤ) :
    ComplexCondition G F₁ F₂ (fun M N ↦ (τ.app M).app N) P Q
      (ComplexComparison G F₁ F₂ τ P Q) := by
  intro r s n h
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX τ (.up ℤ) P Q r s n h

end ComplexComparisons

private theorem tensorLocalization_isIso (P Q : CochainComplex D ℤ)
    (hQ : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat Q) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient D (.up ℤ)).obj P)
      ((HomotopyCategory.quotient D (.up ℤ)).obj Q)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
      (HomotopyCategory.quasiIso D (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff Q).2 hQ)
  change IsIso ((_ ⊗ₘ _) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
  infer_instance

private noncomputable def mixedTensorCounit (F₁ F₂ : C ⥤ D)
    [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂] :
    (((Functor.whiskeringLeft₂ _).obj (DerivedCategory.Q (C := C))).obj
      DerivedCategory.Q).obj
        ((((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
          F₂.mapDerivedCategory).obj (curriedTensor _)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj
          ((Functor.postcompose₂.obj DerivedCategory.Q).obj (curriedTensor _)) :=
  (((Functor.whiskeringLeft₂ _).map F₁.mapDerivedCategoryFactors.hom).app
      (DerivedCategory.Q ⋙ F₂.mapDerivedCategory)).app (curriedTensor _) ≫
    (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q)).map F₂.mapDerivedCategoryFactors.hom).app (curriedTensor _) ≫
    (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
      (F₂.mapHomologicalComplex (.up ℤ))).map (Functor.LaxMonoidal.μNatTrans DerivedCategory.Q)

private def propertyLocalizer {E : Type*} [Category E]
    (W : MorphismProperty E) (P : ObjectProperty E) :
    LocalizerMorphism (W.inverseImage P.ι) W where
  functor := P.ι
  map := by rfl

private theorem mixedTensor_isLeftDerived (F₁ F₂ : C ⥤ D)
    [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [F₂.PreservesFlat] [F₂.IsLeftAdjoint] :
    ((((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
      F₂.mapDerivedCategory).obj (curriedTensor _)).IsLeftDerivedFunctor₂
        (mixedTensorCounit F₁ F₂)
        (HomologicalComplex.quasiIso C (.up ℤ))
        (HomologicalComplex.quasiIso C (.up ℤ)) := by
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  let P := (HomologicalComplex.quasiIso D (.up ℤ)).kFlat.inverseImage
    (F₂.mapHomologicalComplex (.up ℤ))
  let Φ := propertyLocalizer W P
  have : Φ.functor.Full := inferInstanceAs P.ι.Full
  have : Φ.functor.Faithful := inferInstanceAs P.ι.Faithful
  have : Φ.IsInduced := ⟨rfl⟩
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution C).some
  have hρ (K : CochainComplex C ℤ) : P (Λ.reduced.resolutionFunctor.obj K) :=
    F₂.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ.reduced
      ObjectProperty.flat.essImage_ι_le K
  have : Φ.IsLeftDerivabilityStructure :=
    Φ.isLeftDerivabilityStructure_of_functorial_resolutions
      (ρ := ObjectProperty.lift P Λ.reduced.resolutionFunctor hρ)
      Λ.reduced.resolutionNatTrans
      (fun K ↦ by
        change HomologicalComplex.quasiIso C (.up ℤ) _
        rw [HomologicalComplex.mem_quasiIso_iff]
        exact Λ.reduced.quasiIso_resolutionNatTrans_app K) rfl
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (LocalizerMorphism.id W) Φ (mixedTensorCounit F₁ F₂) (fun K L ↦ ?_)
  have := tensorLocalization_isIso
    ((F₁.mapHomologicalComplex (.up ℤ)).obj K)
    ((F₂.mapHomologicalComplex (.up ℤ)).obj L.obj) L.property
  simp only [mixedTensorCounit, NatTrans.comp_app]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance this)

/-- Families of morphisms between the derived tensor images.
Source: blueprint derived tensor comparison (blueprint: lem-pur-derived-tensor-comparison). -/
noncomputable def ComparisonHom
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂] : Type _ :=
  ∀ M N : DerivedCategory C,
      G.mapDerivedCategory.obj (M ⊗ N) ⟶
        F₁.mapDerivedCategory.obj M ⊗ F₂.mapDerivedCategory.obj N

/-- Reexpress a comparison family using an explicitly presented tensor bifunctor.
Source: blueprint derived tensor normalization
(blueprint: lem-pur-derived-tensor-comparison). -/
theorem comparisonHom_tensor
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (T : DerivedCategory D ⥤ DerivedCategory D ⥤ DerivedCategory D)
    (h : ∀ S M N : DerivedCategory D,
      (S ⟶ M ⊗ N) = (S ⟶ (T.obj M).obj N)) :
    ComparisonHom G F₁ F₂ =
      (∀ M N : DerivedCategory C,
        G.mapDerivedCategory.obj (M ⊗ N) ⟶
          (T.obj (F₁.mapDerivedCategory.obj M)).obj (F₂.mapDerivedCategory.obj N)) := by
  have e : (fun M N : DerivedCategory C ↦
      (G.mapDerivedCategory.obj (M ⊗ N) ⟶
        F₁.mapDerivedCategory.obj M ⊗ F₂.mapDerivedCategory.obj N)) =
      (fun M N : DerivedCategory C ↦
        (G.mapDerivedCategory.obj (M ⊗ N) ⟶
          (T.obj (F₁.mapDerivedCategory.obj M)).obj (F₂.mapDerivedCategory.obj N))) := by
    funext M N
    exact h _ _ _
  exact congrArg
    (fun E : DerivedCategory C → DerivedCategory C → Type (u + 1) ↦ ∀ M N, E M N) e

omit [HasDerivedCategory D] [Abelian.HasFunctorialFlatResolution D] in
/-- The monoidal tensor on cochain complexes is the signed total tensor.
Source: blueprint signed total tensor (blueprint: lem-pur-derived-tensor-comparison). -/
theorem complexTensor_eq (P Q : CochainComplex D ℤ) :
    P ⊗ Q = HomologicalComplex.tensorObj P Q := rfl

private theorem tensorLocalization_model_eq (P Q : CochainComplex D ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q ≫
        DerivedCategory.Q.map (eqToHom (complexTensor_eq P Q)) =
      Functor.LaxMonoidal.μ DerivedCategory.Q P Q := by
  have h : eqToHom (complexTensor_eq P Q) = 𝟙 (P ⊗ Q) := rfl
  rw [h, CategoryTheory.Functor.map_id, Category.comp_id]

/-- Naturality and normalization on all complex models, retaining the signed total tensor.
Source: blueprint derived tensor comparison (blueprint: lem-pur-derived-tensor-comparison). -/
noncomputable def ComparisonFamilyCondition
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (θ : ∀ P Q : CochainComplex C ℤ, ComplexHom G F₁ F₂ P Q)
    (t : ComparisonHom G F₁ F₂) : Prop :=
  (∀ (M M' N N' : DerivedCategory C) (a : M ⟶ M') (b : N ⟶ N'),
        G.mapDerivedCategory.map (a ⊗ₘ b) ≫ t M' N' =
          t M N ≫
            ((curriedTensor (DerivedCategory D)).map (F₁.mapDerivedCategory.map a)).app
              (F₂.mapDerivedCategory.obj N) ≫
            ((curriedTensor (DerivedCategory D)).obj
              (F₁.mapDerivedCategory.obj M')).map (F₂.mapDerivedCategory.map b)) ∧
      (∀ P Q : CochainComplex C ℤ,
        G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          G.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
          DerivedCategory.Q.map (θ P Q) =
        t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
          (((curriedTensor (DerivedCategory D)).map
            (F₁.mapDerivedCategoryFactors.hom.app P)).app
              (F₂.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)) ≫
            ((curriedTensor (DerivedCategory D)).obj
              (DerivedCategory.Q.obj ((F₁.mapHomologicalComplex (.up ℤ)).obj P))).map
                (F₂.mapDerivedCategoryFactors.hom.app Q)) ≫
          (Functor.LaxMonoidal.μ DerivedCategory.Q
            ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
            ((F₂.mapHomologicalComplex (.up ℤ)).obj Q) ≫
          DerivedCategory.Q.map (eqToHom (complexTensor_eq
            ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
            ((F₂.mapHomologicalComplex (.up ℤ)).obj Q)))))

/-- Naturality and model normalization for a natural tensor comparison.
Source: blueprint K-flat descent (blueprint: lem-pur-derived-tensor-comparison). -/
noncomputable def ComparisonCondition
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _))
    (t : ComparisonHom G F₁ F₂) : Prop :=
  ComparisonFamilyCondition G F₁ F₂ (fun P Q ↦ (τ.app P).app Q) t

/-- A natural comparison of tensor complexes descends uniquely to the derived tensor.
Source: blueprint supported exterior product, K-flat descent.
(blueprint: lem-pur-derived-tensor-comparison).
Proof: resolve the second variable by functorial flat complexes. Since F₂ preserves
flat objects and colimits, their images are K-flat. The mixed target tensor is therefore
a total left derived bifunctor, with counit the two exact-functor comparisons followed
by the tensor-localization counit. Apply its universal property to the image under G
of the source tensor counit followed by the given comparison. Its factorization equation
is the displayed model normalization. Naturality comes from the resulting natural
transformation. Conversely, a normalized natural family gives a natural transformation;
the uniqueness part of the same universal property identifies it with the constructed one. -/
theorem exists_unique_comparison
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [F₂.PreservesFlat] [F₂.IsLeftAdjoint]
    (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _)) :
    ∃! t : ComparisonHom G F₁ F₂,
      ComparisonCondition G F₁ F₂ τ t := by
  unfold ComparisonHom ComparisonCondition ComparisonFamilyCondition
  simp only [tensorLocalization_model_eq, curriedTensor_obj_map,
    curriedTensor_map_app, ← tensorHom_def]
  let U := (Functor.postcompose₂.obj G.mapDerivedCategory).obj
    (curriedTensor (DerivedCategory C))
  let V := (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
    F₂.mapDerivedCategory).obj (curriedTensor (DerivedCategory D))
  let α := mixedTensorCounit F₁ F₂
  have : V.IsLeftDerivedFunctor₂ α (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)) := mixedTensor_isLeftDerived F₁ F₂
  let β := (Functor.postcompose₂.obj G.mapDerivedCategory).map
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Q) ≫
    (Functor.postcompose₂.map G.mapDerivedCategoryFactors.hom).app
      (curriedTensor (CochainComplex C ℤ)) ≫
    Functor.postcompose₂MapWhiskeringLeft₂ τ DerivedCategory.Q
  let γ : U ⟶ V := V.leftDerived₂Lift α
    (HomologicalComplex.quasiIso C (.up ℤ))
    (HomologicalComplex.quasiIso C (.up ℤ)) U β
  have hγ (P Q : CochainComplex C ℤ) :=
    V.leftDerived₂_fac_app_app α (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)) U β P Q
  have hα (P Q : CochainComplex C ℤ) : (α.app P).app Q =
      (F₁.mapDerivedCategoryFactors.hom.app P ⊗ₘ
        F₂.mapDerivedCategoryFactors.hom.app Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
          ((F₂.mapHomologicalComplex (.up ℤ)).obj Q) := by
    simp only [α, mixedTensorCounit, NatTrans.comp_app,
      MonoidalCategory.tensorHom_def, Category.assoc]
    rfl
  have hβ (P Q : CochainComplex C ℤ) : (β.app P).app Q =
      G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        G.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
        DerivedCategory.Q.map ((τ.app P).app Q) := by rfl
  refine ⟨fun M N ↦ (γ.app M).app N, ⟨?_, ?_⟩, ?_⟩
  · intro M M' N N' a b
    have ha := congr_app (γ.naturality a) N
    have hb := (γ.app M').naturality b
    change G.mapDerivedCategory.map (a ▷ N) ≫ (γ.app M').app N =
      (γ.app M).app N ≫ (F₁.mapDerivedCategory.map a ▷ F₂.mapDerivedCategory.obj N) at ha
    change G.mapDerivedCategory.map (M' ◁ b) ≫ (γ.app M').app N' =
      (γ.app M').app N ≫ (F₁.mapDerivedCategory.obj M' ◁ F₂.mapDerivedCategory.map b) at hb
    rw [MonoidalCategory.tensorHom_def, CategoryTheory.Functor.map_comp, Category.assoc, hb,
      ← Category.assoc, ha, Category.assoc, ← MonoidalCategory.tensorHom_def]
  · intro P Q
    have h := hγ P Q
    rw [hα, hβ] at h
    exact h.symm
  · intro t ht
    let δ : U ⟶ V :=
      { app M :=
          { app N := t M N
            naturality N N' b := by
              change G.mapDerivedCategory.map (M ◁ b) ≫ t M N' =
                t M N ≫ (F₁.mapDerivedCategory.obj M ◁ F₂.mapDerivedCategory.map b)
              simpa only [id_tensorHom, CategoryTheory.Functor.map_id] using
                ht.1 M M N N' (𝟙 M) b }
        naturality M M' a := by
          apply NatTrans.ext
          funext N
          change G.mapDerivedCategory.map (a ▷ N) ≫ t M' N =
            t M N ≫ (F₁.mapDerivedCategory.map a ▷ F₂.mapDerivedCategory.obj N)
          simpa only [tensorHom_id, CategoryTheory.Functor.map_id] using
            ht.1 M M' N N a (𝟙 N) }
    have he : δ = γ := by
      apply V.leftDerived₂_ext α (HomologicalComplex.quasiIso C (.up ℤ))
        (HomologicalComplex.quasiIso C (.up ℤ)) U
      apply NatTrans.ext
      funext P
      apply NatTrans.ext
      funext Q
      change t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫ (α.app P).app Q = _
      rw [hα]
      have h := hγ P Q
      rw [hβ] at h
      exact (ht.2 P Q).symm.trans h.symm
    exact congrArg (fun η : U ⟶ V ↦ fun M N ↦ (η.app M).app N) he

end AbstractDerivedTensor

end AlgebraicGeometry.ProEtale.SupportedTensorDerivation
