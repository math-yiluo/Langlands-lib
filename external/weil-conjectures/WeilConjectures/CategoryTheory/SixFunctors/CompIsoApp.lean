/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! # Pointwise comparison with explicit composite objects -/

@[expose] public section
set_option autoImplicit false

namespace CategoryTheory.Functor

/-- Apply an isomorphism between composite functors with both object expressions
written explicitly. This is `Iso.app`; the explicit object interface prevents
conversion from unfolding a concrete derived functor before reducing a functor
composition. Source: the exact-derived composition square in diagonal coefficient
changes (1), using Mathlib's natural-isomorphism application.
(blueprint: def-diagonal-composite-iso-pointwise). -/
@[irreducible]
def compIsoApp {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    {F : C ⥤ D} {G : D ⥤ V} {H : C ⥤ E} {I : E ⥤ V}
    (e : F ⋙ G ≅ H ⋙ I) (M : C) : G.obj (F.obj M) ≅ I.obj (H.obj M) :=
  e.app M

end CategoryTheory.Functor
