/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Injective module sheaves are injective presheaves

Source: literature/stacks-project/sites-cohomology.tex, Lemma Tag 03FB
(blueprint: lem-weil-pbc-ringed-site-injective-module-injective-presheaf).
-/

@[expose] public section

universe u v w t

open CategoryTheory

namespace CategoryTheory

/-- For a ringed site, an injective sheaf of modules is injective as its underlying
presheaf of modules. The assertion is the exact-sheafification adjunction argument.
Source: Stacks Project, Lemma Tag 03FB.
(blueprint: lem-weil-pbc-ringed-site-injective-module-injective-presheaf)

Proof:
1. The module sheafification functor `PresheafOfModules.sheafification (𝟙 R.obj)` is left
   adjoint to the inclusion, by `PresheafOfModules.sheafificationAdjunction`
   (def-weil-presheaf-modules-sheafification). It is exact
   (lem-weil-pbc-ringed-site-module-sheafification-exact), so it preserves monomorphisms.
2. Apply `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`
   (lem-sp-right-adjoint-preserves-injectives) to this adjunction. Since `I` is injective
   (def-sp-injective-resolutions) in the sheaf category (situation-conventions),
   its underlying presheaf is injective. The right adjoint for the identity ring map is
   the inclusion followed by identity restriction of scalars, canonically the inclusion.
-/
theorem injective_module_sheaf_injective_presheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w})
    [HasSheafify J AddCommGrpCat.{t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
    (I : SheafOfModules.{t} R) [Injective I] :
    Injective ((SheafOfModules.forget R).obj I) := by
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).map_injective I
    inferInstance

end CategoryTheory
