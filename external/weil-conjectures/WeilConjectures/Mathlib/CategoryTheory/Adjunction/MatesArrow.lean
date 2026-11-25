/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Counits and base change

Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be adjunctions and `α : G ⋙ L₂ ⟶ L₁ ⋙ H` a natural transformation,
with mate `β : R₁ ⋙ G ⟶ H ⋙ R₂` (the base change morphism). If `α` and `β` are isomorphisms at
the relevant objects, then `H` applied to the counit of `L₁ ⊣ R₁` at `d` is isomorphic, as an
arrow, to the counit of `L₂ ⊣ R₂` at `H d`.

## Main statements

- `CategoryTheory.Adjunction.arrowIsoMapCounit`
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- **Base change of a counit.** If the square `α : G ⋙ L₂ ⟶ L₁ ⋙ H` is invertible at `R₁ d` and
its mate, the base change morphism `G (R₁ d) ⟶ R₂ (H d)`, is invertible, then `H (ε₁ d)` and
`ε₂ (H d)` are isomorphic arrows. -/
noncomputable def arrowIsoMapCounit (α : TwoSquare G L₁ L₂ H) (d : D) [IsIso (α.app (R₁.obj d))]
    [IsIso ((mateEquiv adj₁ adj₂ α).app d)] :
    Arrow.mk (H.map (adj₁.counit.app d)) ≅ Arrow.mk (adj₂.counit.app (H.obj d)) :=
  Arrow.isoMk (asIso (inv (α.app (R₁.obj d)) ≫ L₂.map ((mateEquiv adj₁ adj₂ α).app d)))
    (Iso.refl _) (by
      simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, asIso_hom, Category.assoc,
        mateEquiv_counit, IsIso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id])

end CategoryTheory.Adjunction
