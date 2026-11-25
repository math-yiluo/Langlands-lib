/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The counit of an adjunction at a cokernel

Let `F ⊣ G` be an adjunction such that `G ⋙ F` preserves cokernels. If the counit is invertible
at the source and the target of a morphism `g`, it is invertible at the cokernel of `g`: under
`F (G (coker g)) ≅ coker (F (G g))` it is the morphism of cokernels induced by the counit.

## Main results

- `CategoryTheory.Adjunction.isIso_counit_app_cokernel`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- If `G ⋙ F` preserves cokernels and the counit of `F ⊣ G` is invertible at the source and
the target of `g`, it is invertible at the cokernel of `g`. -/
lemma isIso_counit_app_cokernel (adj : F ⊣ G) [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] [HasCokernels D]
    [PreservesColimitsOfShape WalkingParallelPair (G ⋙ F)] {Q₁ Q₂ : D} (g : Q₁ ⟶ Q₂)
    [IsIso (adj.counit.app Q₁)] [IsIso (adj.counit.app Q₂)] :
    IsIso (adj.counit.app (cokernel g)) := by
  let e := PreservesCokernel.iso (G ⋙ F) g
  have key : e.inv ≫ adj.counit.app (cokernel g) =
      cokernel.map _ _ (adj.counit.app Q₁) (adj.counit.app Q₂) (adj.counit.naturality g) := by
    refine coequalizer.hom_ext ?_
    rw [PreservesCokernel.iso_inv, ← Category.assoc, π_comp_cokernelComparison, cokernel.π_desc]
    exact adj.counit.naturality (cokernel.π g)
  have h : adj.counit.app (cokernel g) = e.hom ≫ (e.inv ≫ adj.counit.app (cokernel g)) :=
    (Iso.hom_inv_id_assoc _ _).symm
  rw [h, key]
  infer_instance

end CategoryTheory.Adjunction
