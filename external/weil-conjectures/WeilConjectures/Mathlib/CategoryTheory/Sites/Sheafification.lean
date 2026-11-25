/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Sheafification

Ported from the `proetale` package (`Proetale.Mathlib.CategoryTheory.Sites.Sheafification`).
-/

@[expose] public section

namespace CategoryTheory

/-- If `G : I ⥤ (Cᵒᵖ ⥤ A)` takes values in `J`-sheafs, the post-composition with
sheafification and inclusion is isomorphic to `G`. -/
noncomputable
def presheafToSheafSheafToPresheafIso {C I A : Type*} [Category* C]
    [Category* I] [Category* A] (J : GrothendieckTopology C) [HasWeakSheafify J A]
    (G : I ⥤ (Cᵒᵖ ⥤ A)) (H : ∀ (i : I), Presheaf.IsSheaf J (G.obj i)) :
    G ⋙ presheafToSheaf J A ⋙ sheafToPresheaf J A ≅ G :=
  NatIso.ofComponents (fun i ↦ (isoSheafify _ (H _)).symm) <| by
    intro i j u
    apply sheafify_hom_ext _ _ _ (H _)
    simp

end CategoryTheory
