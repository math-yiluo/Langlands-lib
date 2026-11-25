/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GradedObject.Bifunctor

/-!
# The bifunctor on graded objects, compared with `mapBifunctor`

Supplement to `Mathlib.CategoryTheory.GradedObject.Bifunctor`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃)

namespace GradedObject

variable {I J K : Type*} (p : I × J → K)

set_option backward.isDefEq.respectTransparency false in
@[simps!]
noncomputable def mapBifunctorMapIso
    [∀ (j : K), HasColimitsOfShape (Discrete ↑(p ⁻¹' {j})) C₃] :
    mapBifunctorMap F p ≅
      mapBifunctor F I J ⋙ (Functor.whiskeringRight _ _ _).obj (map C₃ p) :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents (fun Y ↦ Iso.refl _) (fun ψ ↦ by
      ext k
      simp [mapBifunctorMapMap]))
    (fun φ ↦ by
      ext Y k
      simp [mapBifunctorMapMap])

end GradedObject

end CategoryTheory
