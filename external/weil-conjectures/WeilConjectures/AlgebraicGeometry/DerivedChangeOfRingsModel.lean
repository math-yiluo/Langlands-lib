/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel

/-! # Canonical derived change-of-rings model

Source: Stacks Project Tags 06YT, 06YY and 06XN
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v r wO wS
open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {O S : Sheaf J CommRingCat.{r}} (φ : O ⟶ S)
  [HasDerivedCategory.{wO}
    (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))]
  [HasDerivedCategory.{wS}
    (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S))]

/-- The canonical cochain model selected by the derived change-of-rings existence theorem.

Source: Stacks Project Tags 06YT, 06YY and 06XN
(auxiliary; not a blueprint node). The selected object is the
canonical universal model supplied by `nonempty_derivedChangeOfRingsCochainModel`.
-/
def canonicalDerivedChangeOfRingsModel :
    DerivedChangeOfRingsCochainModel.{u, v, r, wO, wS} φ :=
  Classical.choice (nonempty_derivedChangeOfRingsCochainModel φ)

end SheafOfModules
