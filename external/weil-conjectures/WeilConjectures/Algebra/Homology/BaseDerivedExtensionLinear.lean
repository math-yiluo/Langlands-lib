/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionScalar

/-!
# Linear total derived extension of scalars

Source: Stacks Project, Tag 06Y6, lemma-derived-base-change
(blueprint: lem-pc-base-derived-extension-linear).
-/

@[expose] public section

set_option autoImplicit false

universe uR uB v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable (R : Type uR) (B : Type uB) [CommRing R] [CommRing B]
  [Algebra R B]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} B)]

-- Derived scalar extension is expressed in a common module universe.
/-- Source: Stacks Project, Tag 06Y6, lemma-derived-base-change
(blueprint: lem-pc-base-derived-extension-linear).

Proof: Resolve R-complexes by K-flat complexes on the one-point site. Tensor with B
in degree zero preserves quasi-isomorphisms between K-flat models. Apply the
resolving-class construction on the homotopy category to obtain the total left derived
functor and its universal counit. For unequal ring universes use the canonical module
category equivalences with the rings lifted to the common carrier universe; these
preserve ordinary extension and quasi-isomorphisms, and hence transport the universal
pair. On K-flat models, tensor extension preserves addition of maps and sends
multiplication by r to multiplication by its image in B. The resolution comparison
isomorphisms and functoriality transport these identities to every derived object.
The derived functor is therefore additive. Apply the additive B-linear homology
functor to the scalar identity to obtain the displayed equality in every degree.
No A-action or comparison to ordinary cohomology is constructed here. -/
theorem exists_baseDerivedExtension_linear
    [(extendScalars.{_, _, max uR uB v} (algebraMap R B)).Additive] :
    ∃ (derived : DerivedCategory (ModuleCat.{max uR uB v} R) ⥤
        DerivedCategory (ModuleCat.{max uR uB v} B))
      (counit : DerivedCategory.Qh ⋙ derived ⟶
        (extendScalars.{_, _, max uR uB v} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh),
      derived.IsLeftDerivedFunctor counit
        (HomotopyCategory.quasiIso (ModuleCat.{max uR uB v} R) (.up ℤ)) ∧
      derived.Additive ∧
      ∀ (i : ℤ) (E : CochainComplex (ModuleCat.{max uR uB v} R) ℤ) (r : R),
        (DerivedCategory.homologyFunctor (ModuleCat.{max uR uB v} B) i).map
          (derived.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient _ _).map (r • 𝟙 E)))) =
        algebraMap R B r • 𝟙
          ((DerivedCategory.homologyFunctor (ModuleCat.{max uR uB v} B) i).obj
            (derived.obj (DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient _ _).obj E)))) := by
  obtain ⟨L, ε, hL, ⟨c, htri⟩, hres⟩ := exists_baseDerivedExtension_resolution R B
  let := c
  let := htri
  refine ⟨L, ε, hL, inferInstance, ?_⟩
  exact baseDerivedExtension_scalar R B L ε hres

end ModuleCat
