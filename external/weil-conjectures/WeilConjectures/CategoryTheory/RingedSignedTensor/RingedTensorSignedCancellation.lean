/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.SmoothPurity.CoefficientClosedStructure.CoefficientClosedTensorComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # Signed cancellation in an arbitrary normalized closed tensor presentation

Source: Stacks 0A8X and 08JC. The native tensor shifts are transported through the
canonical evaluation-preserving comparison of closed tensor presentations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite WeilConjectures SheafOfModules

namespace CategoryTheory.RingedSignedTensor

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The native ringed module category.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
abbrev Modules := RingedDerivedNative.Modules.{c, v, r} J R

variable [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

/-- The native tensor, with the monoidal presentation explicitly retained.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
def nativeTensor : DerivedCategory (Modules.{c, v, r} J R) ×
    DerivedCategory (Modules.{c, v, r} J R) ⥤ DerivedCategory (Modules.{c, v, r} J R) :=
  @tensor _ _ (RingedDerivedNative.monoidal.{c, v, r, w} J R)

/-- The proved native closed structure, retaining its recorded evaluation model.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
def nativeClosed :
    CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R) :=
  (RingedDerivedNative.closedAdjunction.{c, v, r, w} J R).choose

/-- The closed structure uses exactly the native monoidal structure.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
theorem nativeClosed_monoidal :
    (nativeClosed.{c, v, r, w} J R).monoidal = RingedDerivedNative.monoidal.{c, v, r, w} J R :=
  (RingedDerivedNative.closedAdjunction.{c, v, r, w} J R).choose_spec.1

/-- The evaluation-preserving comparison with the native tensor.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
def comparison
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R)) :
    S.tensor ≅ nativeTensor.{c, v, r, w} J R :=
  CoefficientClosedStructure.comparison S (nativeClosed.{c, v, r, w} J R) ≪≫
    eqToIso (congrArg (fun m ↦ @tensor _ _ m) (nativeClosed_monoidal.{c, v, r, w} J R))

end CategoryTheory.RingedSignedTensor
