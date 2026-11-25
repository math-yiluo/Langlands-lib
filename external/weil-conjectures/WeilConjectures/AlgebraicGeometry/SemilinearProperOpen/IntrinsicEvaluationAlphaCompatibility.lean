/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenEvaluationSupport
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenEvaluationSupport
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.SemilinearProperOpenNormalization
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOpenBaseChangeEvaluation
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingClopenArrowEvaluation
import WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization

/-! # Evaluation compatibility of the intrinsic inverse-image clopen word

## References

* Stacks Project, Tag 0F7B, open case
* Zheng, Construction 4.1 and Lemma 4.10
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
open Normalization
namespace GenericComposition
private def composeComparison
    {A B D A' B' D' : Type*}
    [Category A] [Category B] [Category D]
    [Category A'] [Category B'] [Category D']
    {F : A ⥤ B} {G : B ⥤ D} {F' : A' ⥤ B'} {G' : B' ⥤ D'}
    {U : A ⥤ A'} {V : B ⥤ B'} {W : D ⥤ D'}
    (f : F ⋙ V ≅ U ⋙ F') (g : G ⋙ W ≅ V ⋙ G') :
    (F ⋙ G) ⋙ W ≅ U ⋙ (F' ⋙ G') :=
  Functor.associator F G W ≪≫ Functor.isoWhiskerLeft F g ≪≫
    (Functor.associator F V G').symm ≪≫ Functor.isoWhiskerRight f G' ≪≫
    Functor.associator U F' G'

end GenericComposition
open GenericComposition

section ExactEvaluation
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategoryNatIso
variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category A₀] [Category A₁] [Category A₂]
  [Category B₀] [Category B₁] [Category B₂]
  [Abelian A₀] [Abelian A₁] [Abelian A₂]
  [Abelian B₀] [Abelian B₁] [Abelian B₂]
  [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂]
  [HasDerivedCategory B₀] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
  (F₀₁ : A₀ ⥤ A₁) (F₁₂ : A₁ ⥤ A₂) (F₀₂ : A₀ ⥤ A₂)
  (G₀₁ : B₀ ⥤ B₁) (G₁₂ : B₁ ⥤ B₂) (G₀₂ : B₀ ⥤ B₂)
  (U₀ : A₀ ⥤ B₀) (U₁ : A₁ ⥤ B₁) (U₂ : A₂ ⥤ B₂)
  [F₀₁.Additive] [F₁₂.Additive] [F₀₂.Additive]
  [G₀₁.Additive] [G₁₂.Additive] [G₀₂.Additive]
  [U₀.Additive] [U₁.Additive] [U₂.Additive]
  [PreservesFiniteLimits F₀₁] [PreservesFiniteColimits F₀₁]
  [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
  [PreservesFiniteLimits F₀₂] [PreservesFiniteColimits F₀₂]
  [PreservesFiniteLimits G₀₁] [PreservesFiniteColimits G₀₁]
  [PreservesFiniteLimits G₁₂] [PreservesFiniteColimits G₁₂]
  [PreservesFiniteLimits G₀₂] [PreservesFiniteColimits G₀₂]
  [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]

end ExactEvaluation

section ConstantEvaluation
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryNatIso

variable {A B D F : Type*} [Category A] [Category B] [Category D] [Category F]
  [Abelian A] [Abelian B] [Abelian D] [Abelian F]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory D] [HasDerivedCategory F]
  [HasDerivedCategory (ℕᵒᵖ ⥤ D)] [HasDerivedCategory (ℕᵒᵖ ⥤ F)]
  (L : A ⥤ B) (G : B ⥤ D) (H : A ⥤ F) (I : F ⥤ D)
  [L.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ F D).obj I)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ F D).obj I)]

end ConstantEvaluation

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
variable (n : ℕ)
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf alpha gamma
set_option synthInstance.maxSize 4096
attribute [local irreducible] Functor.mapDerivedCategoryNatIso
  HasDerivedCategory.standard DerivedCategory.Q
  Functor.mapDerivedCategoryFactors SemilinearSections.systemRing
  coefficientMap VaryingRing.ringMap
  Functor.rightDerivedFunctorIsoMapDerivedCategory
attribute [local implicit_reducible] VaryingRing.coefficientTransition
  StrictTower.G StrictTower.R P R

private local instance (priority := 50000) fixedSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1}

private local instance (priority := 50000) fixedLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}

private local instance (priority := 40000) fixedAbelian (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Abelian (proEtaleRingModules X R) :=
  @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} X.ProEt inferInstance
    (ProEt.topology X)
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    (SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1})
    (SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1})

attribute [local instance 30000] StrictTower.clopenTowerAbelian
attribute [local instance 20000] StrictTower.towers_hasDerivedCategory
  proEtaleRingModules_hasDerivedCategory

private local instance levelTower_additive (X : Scheme.{u}) :
    (levelTower C τ n X).Additive := by
  dsimp only [levelTower]
  infer_instance

private local instance levelTower_limits (X : Scheme.{u}) :
    PreservesFiniteLimits (levelTower C τ n X) := by
  dsimp only [levelTower]
  infer_instance

private local instance levelTower_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (levelTower C τ n X) := by
  dsimp only [levelTower]
  infer_instance

private def normalizedPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    VaryingRing.G.{u} C τ f ⋙ E C τ n X ≅ E C τ n Y ⋙ StrictTower.G.{u} (C n) f :=
  Functor.mapDerivedCategorySquareIso
    (SemilinearProperOpenCoreAliases.constant_diagram_square
      (VaryingRing.pull.{u} C τ f) (VaryingRing.eval.{u} C τ X n)
      (VaryingRing.eval.{u} C τ Y n) (StrictTower.modulePullback.{u} (C n) f)
      (VaryingRing.moduleEvalG.{u} C τ f n))

-- Comparing chosen ordinary adjoints requires additional normalization.
attribute [local irreducible] VaryingRing.alpha StrictTower.alpha

-- The categorical cube specializes six exact derived paths.
-- The dependent transport retains the four specified chosen-adjoint comparisons.
end AlgebraicGeometry.ProEtale.SemilinearProperOpen
