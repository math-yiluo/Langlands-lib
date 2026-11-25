/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Right adjoints of left exact functors preserve injective objects

If `u : C ⥤ D` preserves finite limits (for instance, if `u` is an exact functor between abelian
categories) and `u ⊣ u'`, then `u'` sends injective objects to injective objects: `u` preserves
monomorphisms, so this is Mathlib's
`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D]

/-- **Right adjoints of exact functors preserve injectives.** If `u : C ⥤ D` preserves finite
limits (e.g. `u` is an exact functor between abelian categories) and admits a right adjoint `u'`,
then `u'` sends injective objects to injective objects. Indeed, by adjunction, injectivity of
`u' I` amounts to the surjectivity of `Hom(u M', I) ⟶ Hom(u M, I)` for monomorphisms `M ⟶ M'`,
which holds since `u` preserves monomorphisms and `I` is injective.

(blueprint: `lem-sp-right-adjoint-preserves-injectives`) -/
theorem Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits {u : C ⥤ D} {u' : D ⥤ C}
    (adj : u ⊣ u') [PreservesFiniteLimits u] : u'.PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj

end CategoryTheory
