/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.Bifunctor

/-!
# Total tensor with two coefficient rings

Source: Stacks Project, More on Algebra, Section 06Y5 preceding Lemma 06Y6
(blueprint: def-pc-mixed-total-tensor).

## Main definitions

- `ModuleCat.mixedTensor`: tensor over `R`, with the `A`-action through the first factor.
- `ModuleCat.mixedTotalTensor`: its total cochain complex bifunctor.

## Main statements

- `ModuleCat.mixedTensor_preservesZeroMorphisms`: zero preservation in the first variable.
- `ModuleCat.mixedTensor_obj_preservesZeroMorphisms`: zero preservation in the second variable.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace ModuleCat

/-- (blueprint: def-pc-mixed-total-tensor) The bifunctor `(M, E) ↦ M ⊗_A (A ⊗_R E)`,
canonically `M ⊗_R E`, with its `A`-module structure through `M`.
Source: Stacks Project, Section 06Y5, construction preceding Lemma 06Y6. -/
noncomputable abbrev mixedTensor {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} A :=
  curriedTensor (ModuleCat.{u} A) ⋙
    (Functor.whiskeringLeft _ _ _).obj (extendScalars f)

/-- (blueprint: def-pc-mixed-total-tensor) The mixed module tensor preserves zero
morphisms in its first variable. Source: Stacks Project, Section 06Y5.
Proof: extension of scalars and tensoring are additive, so their composite is additive. -/
@[instance] theorem mixedTensor_preservesZeroMorphisms {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : (mixedTensor f).PreservesZeroMorphisms := by
  infer_instance

/-- (blueprint: def-pc-mixed-total-tensor) The mixed module tensor preserves zero
morphisms in its second variable. Source: Stacks Project, Section 06Y5.
Proof: extension of scalars and tensoring with the fixed module are additive. -/
@[instance] theorem mixedTensor_obj_preservesZeroMorphisms {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (X : ModuleCat.{u} A) : ((mixedTensor f).obj X).PreservesZeroMorphisms := by
  refine ⟨?_⟩
  intro Y Z
  have h : (extendScalars f).map (0 : Y ⟶ Z) = 0 := by
    apply ExtendScalars.hom_ext
    intro y
    simp [ExtendScalars.map_tmul]
  dsimp [mixedTensor]
  rw [h]
  simp

/-- (blueprint: def-pc-mixed-total-tensor) The total tensor bifunctor on complexes, with
terms `⨁_{p+q=n} Mᵖ ⊗_R Eᑫ` and differential `d_M ⊗ 1 + (-1)^p 1 ⊗ d_E`.
Source: Stacks Project, Section 06Y5 and Lemma 06Y6. -/
noncomputable def mixedTotalTensor {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤
      CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  (mixedTensor f).map₂CochainComplex

end ModuleCat
