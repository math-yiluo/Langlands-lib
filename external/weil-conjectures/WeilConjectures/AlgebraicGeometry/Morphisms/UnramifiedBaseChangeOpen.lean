/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Base change and restriction of unramified morphisms

## References

* Stacks Project, Morphisms, Lemma 02GA and the final clause of Lemma 02G6
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Stacks Project, Morphisms, Lemma 02GA and the final clause of Lemma 02G6. -/
theorem unramified_baseChange_restrict_open
    {X S S' : Scheme.{u}} (f : X ⟶ S)
    (hf : LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f))
    (g : S' ⟶ S) :
    LocallyOfFiniteType (pullback.snd f g) ∧
      IsOpenImmersion (pullback.diagonal (pullback.snd f g)) ∧
      (∀ (U : X.Opens) (V : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V),
        LocallyOfFiniteType (f.resLE V U hUV) ∧
          IsOpenImmersion (pullback.diagonal (f.resLE V U hUV))) := by
  let : LocallyOfFiniteType f := hf.1
  let : IsOpenImmersion (pullback.diagonal f) := hf.2
  have hfu : FormallyUnramified f := inferInstance
  let : LocallyOfFiniteType (pullback.snd f g) := inferInstance
  let : FormallyUnramified (pullback.snd f g) :=
    MorphismProperty.pullback_snd f g hfu
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro U V hUV
  let : LocallyOfFiniteType (f.resLE V U hUV) := inferInstance
  let : FormallyUnramified (f.resLE V U hUV) :=
    IsZariskiLocalAtSource.resLE hUV hfu
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
