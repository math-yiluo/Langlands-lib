/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape

/-!
# Coherent objects, topoi, and geometric morphisms

Source: Orgogozo, author draft, §8.1, printed pp. 17--18
(blueprint: def-trf-coherent-topos).
-/

@[expose] public section

universe w u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An object is quasi-compact when every epimorphic coproduct onto it has a
finite epimorphic sub-coproduct. Source: Orgogozo, §8.1
(blueprint: def-trf-coherent-topos). -/
def IsQuasiCompactObject {E : Type u} [Category.{v} E]
    [HasCoproducts.{w} E] (A : E) : Prop :=
  ∀ (I : Type w) (B : I → E) (f : ∀ i, B i ⟶ A),
    Epi (Sigma.desc f) →
      ∃ (s : Finset I), Epi (Sigma.desc (fun i : s ↦ f i.1))

end CategoryTheory
