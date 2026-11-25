/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Preservation of colimits by functors out of a reflective subcategory

Let `L ⊣ R` be an adjunction whose counit is an isomorphism, so that every object `Y` is
isomorphic to `L.obj (R.obj Y)`. Then a functor `F` out of the target of `L` preserves colimits
of shape `J` as soon as `L ⋙ F` does, provided the source of `L` has colimits of shape `J`: any
diagram `K` is isomorphic to `(K ⋙ R) ⋙ L`, whose colimit is the image under `L` of the colimit
of `K ⋙ R`.

## Main results

- `CategoryTheory.Adjunction.preservesColimitsOfShape_of_comp`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {L : C ⥤ D} {R : D ⥤ C}

/-- If `L ⊣ R` has an invertible counit and the source of `L` has colimits of shape `J`, a functor
`F` preserves colimits of shape `J` as soon as `L ⋙ F` does. -/
lemma preservesColimitsOfShape_of_comp (adj : L ⊣ R) [IsIso adj.counit] (F : D ⥤ E)
    (J : Type*) [Category* J] [HasColimitsOfShape J C] [PreservesColimitsOfShape J (L ⋙ F)] :
    PreservesColimitsOfShape J F where
  preservesColimit {K} := by
    have := adj.leftAdjoint_preservesColimits
    have : PreservesColimit ((K ⋙ R) ⋙ L) F :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves L (colimit.isColimit (K ⋙ R)))
        (isColimitOfPreserves (L ⋙ F) (colimit.isColimit (K ⋙ R)))
    exact preservesColimit_of_iso_diagram F
      (K.associator R L ≪≫ K.isoWhiskerLeft (asIso adj.counit) ≪≫ K.rightUnitor)

end CategoryTheory.Adjunction
