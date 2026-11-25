/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension

/-!
# Extension of fully faithful functors to Karoubi envelopes

The extension `(functorExtension₂ C D).obj F : Karoubi C ⥤ Karoubi D` of a functor
`F : C ⥤ D` is faithful if `F` is, and full if `F` is fully faithful.
-/

@[expose] public section

namespace CategoryTheory.Idempotents

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

instance faithful_functorExtension₂_obj [F.Faithful] :
    ((functorExtension₂ C D).obj F).Faithful where
  map_injective {P Q} f g h := by
    ext
    exact F.map_injective (by simpa using congrArg Karoubi.Hom.f h)

instance full_functorExtension₂_obj [F.Full] [F.Faithful] :
    ((functorExtension₂ C D).obj F).Full where
  map_surjective {P Q} g := by
    refine ⟨⟨F.preimage g.f, F.map_injective ?_⟩, ?_⟩
    · simpa using g.comm
    · ext
      simp

end CategoryTheory.Idempotents
