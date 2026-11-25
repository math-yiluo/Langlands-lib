/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedSquareData
import all WeilConjectures.CategoryTheory.Exact.ExactDerivedTensorSquare
import WeilConjectures.CategoryTheory.ZetaWeil.RestrictedSquareMonoidal
import WeilConjectures.CategoryTheory.ZetaWeil.RestrictedTransportBraiding
import WeilConjectures.CategoryTheory.SiteInverseImageModuleFlat.SiteInverseImageModuleFlat
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentOrdinaryAbelianSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
import all WeilConjectures.CategoryTheory.Exact.ExactClosedDerivedHom
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # Tensor descent for an ordinary component square -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

section ExactTensor
universe a
variable {A : Type a} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type a} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Braided] [F.PreservesFlat] [F.IsLeftAdjoint]

end ExactTensor

section NormalizedInverse
universe a b v w
variable {A : Type a} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
  {B : Type b} [Category.{w} B] [MonoidalCategory B] [BraidedCategory B]

end NormalizedInverse

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
end

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
