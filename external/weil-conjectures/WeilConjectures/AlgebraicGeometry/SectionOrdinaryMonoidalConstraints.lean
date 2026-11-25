/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors

/-! # The normalized ordinary section functor is strong monoidal

Source: Stacks Project, Modules on Sites, Tag 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local irreducible] ordinaryTensorComparison ordinaryUnitComparison
  Mod.monoidalCategory Mod.monoidalCategoryStruct SheafOfModules.monoidalCategory
  InternalAbelianSheafModule.sectionModuleEquivalence
  SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction

private theorem changeComparisons
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategoryStruct C] [MonoidalCategoryStruct D]
    (E : C ⥤ D) (e e' : E.obj (𝟙_ C) ≅ 𝟙_ D)
    (d d' : ∀ M N : C, E.obj (M ⊗ N) ≅ E.obj M ⊗ E.obj N)
    (he : e = e') (hd : ∀ M N, d M N = d' M N)
    (ha : ∀ M N P, (d (M ⊗ N) P).hom ≫ (d M N).hom ▷ E.obj P ≫
      (α_ _ _ _).hom = E.map (α_ M N P).hom ≫ (d M (N ⊗ P)).hom ≫
        E.obj M ◁ (d N P).hom)
    (hl : ∀ M, (d (𝟙_ C) M).hom ≫ e.hom ▷ E.obj M ≫ (λ_ _).hom =
      E.map (λ_ M).hom)
    (hr : ∀ M, (d M (𝟙_ C)).hom ≫ E.obj M ◁ e.hom ≫ (ρ_ _).hom =
      E.map (ρ_ M).hom) :
    (∀ M N P, (d' (M ⊗ N) P).hom ≫ (d' M N).hom ▷ E.obj P ≫
      (α_ _ _ _).hom = E.map (α_ M N P).hom ≫ (d' M (N ⊗ P)).hom ≫
        E.obj M ◁ (d' N P).hom) ∧
    (∀ M, (d' (𝟙_ C) M).hom ≫ e'.hom ▷ E.obj M ≫ (λ_ _).hom =
      E.map (λ_ M).hom) ∧
    (∀ M, (d' M (𝟙_ C)).hom ≫ E.obj M ◁ e'.hom ≫ (ρ_ _).hom =
      E.map (ρ_ M).hom) := by
  have hd' : d = d' := funext fun M ↦ funext fun N ↦ hd M N
  subst e'
  subst d'
  exact ⟨ha, hl, hr⟩

/-- The normalized ordinary section comparisons preserve associators and unitors.
Source: Stacks Project, Modules on Sites, Tag 03EK; the ordinary tensor and regular
module comparisons in internal_section_tensor_comparison.

Proof: the public internal section tensor comparison theorem supplies coherent
tensor and unit comparisons. They agree with ordinaryTensorComparison and
ordinaryUnitComparison by uniqueness of their pure-tensor and scalar formulas.
Substitute these equalities in its associator and left and right unitor identities.
All three diagrams have the unchanged section equivalence as their forward functor.
No nonzero-ring or flatness hypothesis is used.
(auxiliary; not a blueprint node). -/
theorem section_ordinary_monoidal_constraints (T : Scheme.{u}) :
    (∀ M N P : internalModules Λ T,
      (ordinaryTensorComparison Λ T (M ⊗ N) P).hom ≫
          (ordinaryTensorComparison Λ T M N).hom ▷ (equivalence Λ T).functor.obj P ≫
          (α_ _ _ _).hom =
        (equivalence Λ T).functor.map (α_ M N P).hom ≫
          (ordinaryTensorComparison Λ T M (N ⊗ P)).hom ≫
          (equivalence Λ T).functor.obj M ◁ (ordinaryTensorComparison Λ T N P).hom) ∧
    (∀ M : internalModules Λ T,
      (ordinaryTensorComparison Λ T (𝟙_ (internalModules Λ T)) M).hom ≫
          (ordinaryUnitComparison Λ T).hom ▷ (equivalence Λ T).functor.obj M ≫
          (λ_ _).hom = (equivalence Λ T).functor.map (λ_ M).hom) ∧
    (∀ M : internalModules Λ T,
      (ordinaryTensorComparison Λ T M (𝟙_ (internalModules Λ T))).hom ≫
          (equivalence Λ T).functor.obj M ◁ (ordinaryUnitComparison Λ T).hom ≫
          (ρ_ _).hom = (equivalence Λ T).functor.map (ρ_ M).hom) := by
  obtain ⟨d, e, ht, he, _, ha, hl, hr, _⟩ :=
    (InternalAbelianSheafModule.internal_section_tensor_comparison.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) (condensedRingObj Λ T)).2
  have he' : e = ordinaryUnitComparison Λ T := by
    apply (ordinaryUnitComparison_existsUnique Λ T).unique he
    unfold ordinaryUnitComparison
    exact (ordinaryUnitComparison_existsUnique Λ T).exists.choose_spec
  have hd' (M N : internalModules Λ T) : d M N = ordinaryTensorComparison Λ T M N := by
    apply (ordinaryTensorComparison_existsUnique Λ T M N).unique (ht M N)
    unfold ordinaryTensorComparison
    exact (ordinaryTensorComparison_existsUnique Λ T M N).exists.choose_spec
  exact changeComparisons (equivalence Λ T).functor e (ordinaryUnitComparison Λ T)
    d (ordinaryTensorComparison Λ T) he' hd' ha hl hr

end AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints
