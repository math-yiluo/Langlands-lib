/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# An induction principle for transfinite iterations

Given a successor structure `Φ : SuccStruct C` and a property `P` of objects of `C` which is
closed under isomorphisms, holds for `Φ.X₀`, is preserved by `Φ.succ`, and is closed under
colimits of shape `Set.Iio j` for every limit element `j`, every stage
`(Φ.iterationFunctor J).obj j` of the transfinite iteration of `Φ` satisfies `P`. If moreover
`P` is closed under colimits of shape `J`, then so does the iteration `Φ.iteration J`.

## Main results

* `CategoryTheory.SmallObject.SuccStruct.prop_iterationFunctor_obj`
* `CategoryTheory.SmallObject.SuccStruct.prop_iteration`

-/

@[expose] public section

universe w v u

namespace CategoryTheory.SmallObject.SuccStruct

open Limits

variable {C : Type u} [Category.{v} C] (Φ : SuccStruct C)
  (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]

/-- Induction principle for the stages of the transfinite iteration of a successor
structure: a property closed under isomorphisms which holds for `Φ.X₀`, is preserved by
`Φ.succ` and is closed under the colimits of shape `Set.Iio j` at limit stages `j` holds
for every stage of the iteration diagram
```
Φ.X₀ ⟶ Φ.succ Φ.X₀ ⟶ Φ.succ (Φ.succ Φ.X₀) ⟶ ⋯ ⟶ colim_{i < j} (stage i) ⟶ ⋯
```
-/
lemma prop_iterationFunctor_obj (h₀ : P Φ.X₀) (hsucc : ∀ X, P X → P (Φ.succ X))
    (hlim : ∀ j : J, Order.IsSuccLimit j → P.IsClosedUnderColimitsOfShape (Set.Iio j))
    (j : J) : P ((Φ.iterationFunctor J).obj j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    exact P.prop_of_iso (Φ.iterationFunctorObjBotIso J).symm h₀
  | succ j hj ih =>
    exact P.prop_of_iso (Φ.iterationFunctorObjSuccIso j hj).symm (hsucc _ ih)
  | isSuccLimit j hj ih =>
    have := hlim j hj
    exact P.prop_of_isColimit ((Φ.iterationFunctor J).isColimitOfIsWellOrderContinuous j hj)
      fun i ↦ ih i.1 i.2

/-- If a property of objects satisfies the hypotheses of `prop_iterationFunctor_obj` and is
moreover closed under colimits of shape `J`, then it holds for the iteration
`Φ.iteration J`, the colimit of the iteration diagram
```
Φ.X₀ ⟶ Φ.succ Φ.X₀ ⟶ ⋯ ⟶ (stage j) ⟶ ⋯ ⟶ Φ.iteration J
```
-/
lemma prop_iteration [P.IsClosedUnderColimitsOfShape J] (h₀ : P Φ.X₀)
    (hsucc : ∀ X, P X → P (Φ.succ X))
    (hlim : ∀ j : J, Order.IsSuccLimit j → P.IsClosedUnderColimitsOfShape (Set.Iio j)) :
    P (Φ.iteration J) :=
  P.prop_of_isColimit (Φ.isColimitIterationCocone J)
    (Φ.prop_iterationFunctor_obj J P h₀ hsucc hlim)

end CategoryTheory.SmallObject.SuccStruct
