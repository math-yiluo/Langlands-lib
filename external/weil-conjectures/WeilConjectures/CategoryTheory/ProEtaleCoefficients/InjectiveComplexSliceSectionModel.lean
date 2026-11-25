/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunction
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Compatible slice section models from one injective complex

Source: Stacks Project, `sites-cohomology.tex`, Tag 03F3 and restriction-mapping equation;
`derived.tex`, Tags 05TI, 05TH, 05SA.
(blueprint: lem-pe-injective-complex-slice-section-model)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u w i

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- The actual presheaf of left coefficient modules obtained by restricting scalars
along a map from a constant presheaf of rings. Objects, arrows and maps of sheaves are
unchanged as abelian groups. Source: Stacks, 03F3, sectionwise evaluation.
(blueprint: lem-pe-injective-complex-slice-section-model) -/
def coefficientSectionPresheaf (Λ : Type u) [Ring Λ] (R : Sheaf J RingCat.{u})
    (c : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj) :
    SheafOfModules.{u} R ⥤ Cᵒᵖ ⥤ ModuleCat.{u} Λ where
  obj M :=
    { obj := fun W ↦ ((PresheafOfModules.restrictScalars c).obj M.val).obj W
      map := fun {W V} a ↦ ModuleCat.ofHom
        (X := ((PresheafOfModules.restrictScalars c).obj M.val).obj W)
        (Y := ((PresheafOfModules.restrictScalars c).obj M.val).obj V)
        { toFun := ((PresheafOfModules.restrictScalars c).obj M.val).map a
          map_add' := map_add _
          map_smul' := fun r x ↦
            ((PresheafOfModules.restrictScalars c).obj M.val).map_smul a r x }
      map_id := fun W ↦ by
        ext x
        exact congrArg (fun f ↦ f x)
          (((PresheafOfModules.restrictScalars c).obj M.val).presheaf.map_id W)
      map_comp := fun a b ↦ by
        ext x
        exact congrArg (fun f ↦ f x)
          (((PresheafOfModules.restrictScalars c).obj M.val).presheaf.map_comp a b) }
  map f :=
    { app := fun W ↦ (ModuleCat.restrictScalars (c.app W).hom).map (f.val.app W)
      naturality := fun _ _ a ↦ by
        ext x
        exact PresheafOfModules.naturality_apply f.val a x }

/-- Evaluation with the specified constant scalar action.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
def coefficientSectionEvaluation (Λ : Type u) [Ring Λ] (R : Sheaf J RingCat.{u})
    (c : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj) (W : Cᵒᵖ) :
    SheafOfModules.{u} R ⥤ ModuleCat.{u} Λ :=
  coefficientSectionPresheaf Λ R c ⋙ (evaluation Cᵒᵖ (ModuleCat Λ)).obj W

/-- The canonical coefficient map is the unit of ring sheafification.
Source: Stacks, constant sheaves and 03F3
(blueprint: lem-pe-injective-complex-slice-section-model). -/
abbrev constantCoefficientMap (J : GrothendieckTopology C) (Λ : Type u) [Ring Λ]
    [HasWeakSheafify J RingCat.{u}] :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))

variable (J : GrothendieckTopology C) (Λ : Type u) [Ring Λ]
  [HasWeakSheafify J RingCat.{u}]

/-- The existing module-sheaf category for the constant ring sheaf; a transparent alias.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
abbrev constantModuleSheaves :=
  SheafOfModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Evaluation of constant-ring module sheaves, as a diagram of additive functors.
Source: Stacks, 03F3 (blueprint: lem-pe-injective-complex-slice-section-model). -/
def constantModuleEvaluation (W : Cᵒᵖ) : (constantModuleSheaves J Λ) ⥤ (ModuleCat.{u} Λ) :=
  coefficientSectionEvaluation Λ ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))
    (constantCoefficientMap J Λ) W

variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable [HasDerivedCategory.{w} (constantModuleSheaves J Λ)] [HasDerivedCategory.{w}
  (ModuleCat.{u} Λ)]

variable [∀ W : C, HasDerivedCategory.{w}
  (SheafOfModules.{u} (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).over W))]

-- Comparing the composite derived units requires the full slice-evaluation definitions.
end CategoryTheory
