/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDg.RingedSiteDgModules

/-! The ordinary tensor/restriction construction is the first scalar step.

Source: Stacks sdga, section-dg-bimodules
(blueprint: lem-sfb-ringed-dg-ordinary-extension).

Proof in words: form the balanced sheaf tensor, prove its universal property,
and use the unit inserting `1` and the action map as the ordinary adjunction
unit and counit.  The construction is independent of localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v u

open CategoryTheory

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The balanced sheaf tensor represents ordinary scalar extension, with the
unit inserting one and counit given by the module action.
Source: Stacks sdga, section-dg-bimodules and adjunction-push-pull-dg
(blueprint: lem-sfb-ringed-dg-ordinary-extension).

Proof: coequalize the two A-action maps on the total tensor M tensor B in
B-modules.  Tensor preserves this coequalizer, so it represents balanced,
B-linear maps.  The universal property defines the functor on morphisms.
Sending a map to its value on m tensor 1 and the inverse f(m) times b yields
natural inverse Hom bijections.  These are chain maps by the Leibniz rules.
The unit and counit are the displayed formulas and the triangle identities
reduce to the unit action.  No localization or derived functor is used here.
-/
theorem ordinary_extension_exists
    {O : Sheaf J CommRingCat.{u}} {A B : Algebra.{c, v, u} O} (φ : A ⟶ B) :
    Nonempty (OrdinaryExtension φ) := by
  sorry

end CategoryTheory.RingedSiteDg
