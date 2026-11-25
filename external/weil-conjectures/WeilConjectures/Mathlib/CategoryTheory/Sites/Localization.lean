/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.Plus

/-!
# The plus construction is inverted by sheaves

The map `J.toPlus P : P ⟶ P⁺` belongs to `J.W`, i.e. it is inverted by every sheaf.

## Main results

* `CategoryTheory.GrothendieckTopology.W_toPlus`

-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type w} [Category.{w'} D]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

/-- The map `P ⟶ P⁺` is inverted by every sheaf: every map `g : P ⟶ Q` to a sheaf `Q`
factors uniquely through `J.toPlus P`, via `J.plusLift g`.
```
P ──toPlus──▶ P⁺
  ╲           ┆
   g      plusLift g
    ╲         ┆
     ▼        ▼
        Q
```
-/
lemma W_toPlus (P : Cᵒᵖ ⥤ D) : J.W (J.toPlus P) := by
  intro Q hQ
  refine ⟨fun g₁ g₂ h ↦ ?_, fun g ↦ ⟨J.plusLift g hQ, J.toPlus_plusLift g hQ⟩⟩
  exact (J.plusLift_unique _ hQ g₁ h).trans (J.plusLift_unique _ hQ g₂ rfl).symm

end CategoryTheory.GrothendieckTopology
