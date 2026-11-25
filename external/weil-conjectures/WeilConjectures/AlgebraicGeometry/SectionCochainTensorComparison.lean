/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors

/-! # The normalized comparison with fixed cochain tensor types

Source: Stacks Project, Cohomology on Sites, Tag 07A4 and Modules on Sites, Tag 03EL
(auxiliary; not a blueprint node).

This interface retains the existing summand-normalized totalComparison. Its explicit
source and target use the canonical tensor of cochain complexes. No new tensor or
comparison map is constructed. The existing compact tensor instances live here so
all consumers use the same instance arguments.
-/

/-! The shared interface also retains the canonical cochain unit objects. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option cleanup.letToHave false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing ordinary section tensor with its instance arguments retained.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
instance totalSectionOrdinaryMonoidal (X : Scheme.{u}) :
    MonoidalCategory (modules Λ X) := inferInstance

-- Use the canonical ordinary structure when constructing the cochain caches below.
attribute [-instance] totalSectionOrdinaryMonoidal

/-- The existing graded tensor availability, retained as a compact instance.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
instance totalInternalGraded (X : Scheme.{u})
    (P Q : GradedObject ℤ (internalModules Λ X)) : GradedObject.HasTensor P Q := inferInstance

/-- The existing graded tensor availability for section modules.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
instance totalSectionGraded (X : Scheme.{u})
    (P Q : GradedObject ℤ (modules Λ X)) : GradedObject.HasTensor P Q := inferInstance

/-- The existing canonical iterated tensor property, cached for termwise comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node).
Proof: the ordinary tensor preserves the coproducts defining every graded tensor. -/
instance totalInternalGoodLeft (X : Scheme.{u})
    (P Q H : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q H := inferInstance

/-- The existing canonical iterated tensor property, cached for termwise comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node).
Proof: the ordinary tensor preserves the coproducts defining every graded tensor. -/
instance totalInternalGoodRight (X : Scheme.{u})
    (P Q H : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q H := inferInstance

/-- The existing canonical iterated tensor property, cached for termwise comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node).
Proof: the ordinary tensor preserves the coproducts defining every graded tensor. -/
instance totalInternalTensorFour (X : Scheme.{u})
    (P Q H K : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasTensor₄ObjExt P Q H K := inferInstance

/-- The existing canonical iterated tensor property, cached for termwise comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node).
Proof: the ordinary tensor preserves the coproducts defining every graded tensor. -/
instance totalSectionGoodLeft (X : Scheme.{u})
    (P Q H : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q H := inferInstance

/-- The existing canonical iterated tensor property, cached for termwise comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node).
Proof: the ordinary tensor preserves the coproducts defining every graded tensor. -/
instance totalSectionGoodRight (X : Scheme.{u})
    (P Q H : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q H := inferInstance

/-- The existing canonical iterated tensor property, cached for termwise comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node).
Proof: the ordinary tensor preserves the coproducts defining every graded tensor. -/
instance totalSectionTensorFour (X : Scheme.{u})
    (P Q H K : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasTensor₄ObjExt P Q H K := inferInstance

/-- The existing canonical cochain tensor availability, retained without repeating
instance search through the termwise functors.
Source: Stacks 07A4 (auxiliary; not a blueprint node).
Proof: the graded coproducts defining the cochain tensor already exist. -/
instance (priority := 4000) totalInternalHasTensor (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    HomologicalComplex.HasTensor P Q := inferInstance

/-- The existing canonical cochain tensor availability for section modules.
Source: Stacks 07A4 (auxiliary; not a blueprint node).
Proof: the graded coproducts defining the cochain tensor already exist. -/
instance (priority := 4000) totalSectionHasTensor (X : Scheme.{u})
    (P Q : CochainComplex (modules Λ X) ℤ) :
    HomologicalComplex.HasTensor P Q := inferInstance

/-- The existing signed cochain tensor structure on internal modules.
Source: Stacks 07A4 and 03EL (auxiliary; not a blueprint node). -/
@[reducible] def totalInternalMonoidal (X : Scheme.{u}) :
    MonoidalCategory (CochainComplex (internalModules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategory (internalModules Λ X) (.up ℤ)

attribute [instance] totalInternalMonoidal

/-- The existing signed cochain tensor structure on section modules.
Source: Stacks 07A4 and 03EL (auxiliary; not a blueprint node). -/
@[reducible] def totalSectionMonoidal (X : Scheme.{u}) :
    MonoidalCategory (CochainComplex (modules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategory (modules Λ X) (.up ℤ)

attribute [instance] totalSectionMonoidal

/-- The existing internal cochain tensor data, with the same chosen structure.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[reducible] def totalInternalMonoidalStruct
    (X : Scheme.{u}) : MonoidalCategoryStruct (CochainComplex (internalModules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategoryStruct (internalModules Λ X) (.up ℤ)

attribute [instance 3000] totalInternalMonoidalStruct

/-- The existing section cochain tensor data, with the same chosen structure.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[reducible] def totalSectionMonoidalStruct
    (X : Scheme.{u}) : MonoidalCategoryStruct (CochainComplex (modules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategoryStruct (modules Λ X) (.up ℤ)

attribute [instance 3000] totalSectionMonoidalStruct

/-- The canonical internal cochain unit, retaining its fixed tensor structure.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[implicit_reducible] def internalCochainUnit (T : Scheme.{u}) :
    CochainComplex (internalModules Λ T) ℤ := 𝟙_ _

/-- The canonical section cochain unit, retaining its fixed tensor structure.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[implicit_reducible] def sectionCochainUnit (T : Scheme.{u}) :
    CochainComplex (modules Λ T) ℤ := 𝟙_ _

/-- The object map of a termwise functor, with its cochain value retained.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[reducible] def retainedCochainObject
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (P : CochainComplex C ℤ) :
    CochainComplex D ℤ := (F.mapHomologicalComplex (.up ℤ)).obj P

/-- The morphism map of a termwise functor, with its source and target retained.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[reducible] def retainedCochainMap
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] {P Q : CochainComplex C ℤ} (a : P ⟶ Q) :
    retainedCochainObject F P ⟶ retainedCochainObject F Q :=
  (F.mapHomologicalComplex (.up ℤ)).map a

/-- The original termwise functor, retaining its two data fields separately.
Source: Stacks 07A4 (auxiliary; not a blueprint node).
The data maps and both functor laws are those of mapHomologicalComplex. -/
@[reducible] def retainedCochainFunctor
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] : CochainComplex C ℤ ⥤ CochainComplex D ℤ where
  obj := retainedCochainObject F
  map := retainedCochainMap F
  map_id P := (F.mapHomologicalComplex (.up ℤ)).map_id P
  map_comp a b := (F.mapHomologicalComplex (.up ℤ)).map_comp a b

/-- Retaining the data fields gives exactly the original termwise functor.
Source: Stacks 07A4 (auxiliary; not a blueprint node).
Proof: both functors have identical object and morphism maps; their laws are proofs. -/
theorem retainedCochainFunctor_eq
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    retainedCochainFunctor F = F.mapHomologicalComplex (.up ℤ) := rfl

/-- The fixed section equivalence on cochain complexes, with its functor data cached.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[implicit_reducible] def cochainSectionEquivalence (X : Scheme.{u}) :
    CochainComplex (internalModules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ :=
  retainedCochainFunctor (equivalence Λ X).functor

/-- The normalized total comparison with canonical cochain tensor types.
Source: Stacks 07A4 and 03EL
(auxiliary; not a blueprint node).
The underlying isomorphism is the existing totalComparison, characterized uniquely
on every direct-sum summand by ordinaryTensorComparison. -/
@[irreducible] def cochainTensorComparison (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    (cochainSectionEquivalence Λ X).obj (P ⊗ Q) ≅
      (cochainSectionEquivalence Λ X).obj P ⊗
        (cochainSectionEquivalence Λ X).obj Q :=
  totalComparison Λ X P Q

private theorem generic_total_naturality
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (G : C ⥤ C ⥤ C) [G.Additive] [∀ M : C, (G.obj M).Additive]
    [∀ P Q : CochainComplex C ℤ, CochainComplex.HasMapBifunctor P Q G]
    (H : D ⥤ D ⥤ D) [H.Additive] [∀ M : D, (H.obj M).Additive]
    [∀ P Q : CochainComplex D ℤ, CochainComplex.HasMapBifunctor P Q H]
    (F : C ⥤ D) [F.Additive] [PreservesColimitsOfSize.{0, 0} F]
    (e : ∀ M N : C, F.obj ((G.obj M).obj N) ≅ (H.obj (F.obj M)).obj (F.obj N))
    (he : ∀ {M M' N N' : C} (a : M ⟶ M') (b : N ⟶ N'),
      F.map ((G.map a).app N ≫ (G.obj M').map b) ≫ (e M' N').hom =
        (e M N).hom ≫ (H.map (F.map a)).app (F.obj N) ≫
          (H.obj (F.obj M')).map (F.map b))
    (t : ∀ A B : CochainComplex C ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mapBifunctor A B G) ⟶
        CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj A)
          ((F.mapHomologicalComplex (.up ℤ)).obj B) H)
    (ht : ∀ (A B : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n),
      F.map (CochainComplex.ιMapBifunctor A B G p q n h) ≫ (t A B).f n =
        (e (A.X p) (B.X q)).hom ≫
          CochainComplex.ιMapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj A)
            ((F.mapHomologicalComplex (.up ℤ)).obj B) H p q n h)
    {A A' B B' : CochainComplex C ℤ} (a : A ⟶ A') (b : B ⟶ B') :
    (F.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap a b G (.up ℤ)) ≫ t A' B' =
      t A B ≫ HomologicalComplex.mapBifunctorMap
        ((F.mapHomologicalComplex (.up ℤ)).map a)
        ((F.mapHomologicalComplex (.up ℤ)).map b) H (.up ℤ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map F
  intro p q h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    ← Functor.map_comp_assoc]
  rw [HomologicalComplex.ι_mapBifunctorMap]
  rw [← Category.assoc, Functor.map_comp, Category.assoc, ht,
    reassoc_of% he (a.f p) (b.f q)]
  rw [reassoc_of% ht]
  congr 1
  simpa only [Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_obj_X, Category.assoc] using
    (HomologicalComplex.ι_mapBifunctorMap
      ((F.mapHomologicalComplex (.up ℤ)).map a)
      ((F.mapHomologicalComplex (.up ℤ)).map b) H (.up ℤ) p q n h).symm

private theorem ordinary_naturality (T : Scheme.{u})
    {M M' N N' : internalModules Λ T} (a : M ⟶ M') (b : N ⟶ N') :
    (equivalence Λ T).functor.map (a ⊗ₘ b) ≫ (ordinaryTensorComparison Λ T M' N').hom =
      (ordinaryTensorComparison Λ T M N).hom ≫
        ((equivalence Λ T).functor.map a ⊗ₘ (equivalence Λ T).functor.map b) := by
  have h := InternalAbelianSheafModule.internal_section_tensor_comparison
    (Scheme.ProEt.topology T) (condensedRingObj Λ T)
  rcases h.2 with ⟨e, e₀, data⟩
  have he (V W : internalModules Λ T) : e V W = ordinaryTensorComparison Λ T V W :=
    (ordinaryTensorComparison_existsUnique Λ T V W).unique
      (data.1 V W) (ordinaryTensorComparison_existsUnique Λ T V W).exists.choose_spec
  simpa only [he] using data.2.2.1 M M' N N' a b

/-- Naturality of the existing signed-total comparison in its canonical types.
Source: Stacks 06YN and 07A4
(auxiliary; not a blueprint node).
Proof: ordinaryTensorComparison is the natural comparison supplied by the fixed
internal-section tensor equivalence, by uniqueness of its pure-tensor normalization.
Precompose the desired total equality with each direct-sum inclusion. The defining
summand equation reduces it to ordinary naturality. Coproduct extensionality and the
faithful section equivalence imply equality of the chain maps. -/
theorem cochainTensorComparison_naturality (T : Scheme.{u})
    {A A' B B' : CochainComplex (internalModules Λ T) ℤ} (a : A ⟶ A') (b : B ⟶ B') :
    (cochainSectionEquivalence Λ T).map (a ⊗ₘ b) ≫ (cochainTensorComparison Λ T A' B').hom =
      (cochainTensorComparison Λ T A B).hom ≫
        ((cochainSectionEquivalence Λ T).map a ⊗ₘ (cochainSectionEquivalence Λ T).map b) := by
  dsimp only [cochainSectionEquivalence, retainedCochainFunctor,
    retainedCochainObject, retainedCochainMap] at *
  have ht (P Q : CochainComplex (internalModules Λ T) ℤ)
      (p q n : ℤ) (h : p + q = n) :
      (equivalence Λ T).functor.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q n h) ≫
          (cochainTensorComparison Λ T P Q).hom.f n =
        (ordinaryTensorComparison Λ T (P.X p) (Q.X q)).hom ≫
          CochainComplex.ιMapBifunctor
            (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P)
            (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q)
            (curriedTensor _) p q n h := by
    unfold cochainTensorComparison totalComparison
    exact (totalComparison_existsUnique Λ T P Q).exists.choose_spec p q n h
  change ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.mapBifunctorMap a b (curriedTensor (internalModules Λ T)) (.up ℤ)) ≫
        (cochainTensorComparison Λ T A' B').hom =
    (cochainTensorComparison Λ T A B).hom ≫ HomologicalComplex.mapBifunctorMap
      (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).map a)
      (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).map b)
      (curriedTensor (modules Λ T)) (.up ℤ)
  apply generic_total_naturality (curriedTensor (internalModules Λ T))
    (curriedTensor (modules Λ T)) (equivalence Λ T).functor
    (ordinaryTensorComparison Λ T) ?_
    (fun P Q ↦ (cochainTensorComparison Λ T P Q).hom) ht a b
  intro M M' N N' c d
  simpa only [curriedTensor_map_app, curriedTensor_obj_map,
    ← MonoidalCategory.tensorHom_def, Category.assoc] using ordinary_naturality Λ T c d

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
