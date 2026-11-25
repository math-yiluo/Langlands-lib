/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Normalized finite free scalar models

Source: Stacks Project, sites-modules.tex, Tags 03CY, 03EK and 0GMW.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v s
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

attribute [local irreducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{s} C]
  (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{s}] [HasSheafify J AddCommGrpCat.{s}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  (R : Type s) [CommRing R]

variable [∀ U : C, EssentiallySmall.{s} (Over U)]
  [∀ U : C, HasSheafify (J.over U) CommRingCat.{s}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{s}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{s}]
  {B : Sheaf J CommRingCat.{s}} (φ : scalarPerfectRing J R ⟶ B)

end SheafOfModules
