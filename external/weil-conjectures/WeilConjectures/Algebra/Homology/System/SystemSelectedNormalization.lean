/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequenceTransition
import WeilConjectures.Algebra.Homology.System.SystemDerivedTransitionCoherence
import WeilConjectures.CategoryTheory.SmoothPurity.AdjunctionTransitionCoherence

/-! # Normalization under selected left extension

Source: Zheng, Construction 4.1; integral scalar mates, proof step 2
(blueprint: lem-pur-system-selected-normalization).
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

end SheafOfModules
