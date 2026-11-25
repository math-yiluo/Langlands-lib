/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
public import WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.CofilteredSystem
import all WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement

/-! Internal perfect reduction Hom data. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The termwise scalar model B tensor over constant A with constant P, localized.
The universe lift only enlarges the module carriers, retaining the scalar ring A. -/
def internalPerfectScalarModel (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ) :
    DerivedCategory (AdicCompletion.Modules l E W) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  letI : (FiniteConstantModel.modelFunctor
      (Padic.coefficientExtensionIntegers l E) W).Additive := by
    have : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) :=
      (Padic.coefficientExtensionIntegers_dvr l E).choose_spec.2.2.2.2.2.2.2.2.1
    exact (AdmissibleScalarRealization.pid_scalar_assertions
      (Padic.coefficientExtensionIntegers l E) W).2.1
  let F := ModuleCat.uliftFunctor.{u + 1, u} (Padic.coefficientExtensionIntegers l E) ⋙
    FiniteConstantModel.modelFunctor (Padic.coefficientExtensionIntegers l E) W
  DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)

/-- The scalar complex Q = P dual tensor P. The dual is the signed Hom complex
into A placed in degree zero, and the tensor is the ordinary direct-sum total tensor. -/
def internalPerfectScalarDualTensor
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ) :
    CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ :=
  CochainComplex.mapBifunctor
    (CochainComplex.moduleHomComplex P
      ((CochainComplex.singleFunctor _ 0).obj
        (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionIntegers l E)))) P (curriedTensor _)

/-- Hom at exponent n+1, with the actual derived coefficient extensions. -/
abbrev internalReductionHom (W : Scheme.{u})
    (T K : DerivedCategory (AdicCompletion.Modules l E W)) (n : ℕ) :=
  (AdicCompletion.derivedReduction l E W n).obj T ⟶
    (AdicCompletion.derivedReduction l E W n).obj K

/-- Canonical Hom reduction: alpha_T inverse, extension of f, then alpha_K. -/
def internalReductionHomStep (W : Scheme.{u})
    (T K : DerivedCategory (AdicCompletion.Modules l E W)) (n : ℕ)
    (f : internalReductionHom l E W T K (n + 1)) : internalReductionHom l E W T K n :=
  (AdicCompletion.reductionComp l E W n).inv.app T ≫
    (AdicCompletion.finiteExtend l E W n).map f ≫
    (AdicCompletion.reductionComp l E W n).hom.app K

/-- The Hom inverse system, whose longer arrows are composites of the specified steps. -/
def internalReductionHomTower (W : Scheme.{u})
    (T K : DerivedCategory (AdicCompletion.Modules l E W)) : ℕᵒᵖ ⥤ Type _ :=
  Functor.ofOpSequence (X := fun n ↦ internalReductionHom l E W T K n)
    (fun n ↦ TypeCat.ofHom (internalReductionHomStep l E W T K n))

end AlgebraicGeometry.ProEtale
