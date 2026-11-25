/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Internal homs into a right adjoint of a monoidal functor

Let `F ⊣ G` be an adjunction between monoidal closed categories, with `F` strong monoidal. Then
`[K, G Y] ≅ G [F K, Y]`, naturally in `Y` (`CategoryTheory.Adjunction.ihomCompIso`): both functors
`G ⋙ ihom K` and `ihom (F K) ⋙ G` are right adjoint to `Y ↦ F (K ⊗ Y) ≅ F K ⊗ F Y`.

For the pullback `f^* ⊣ f_*` of sheaves this is the internal form `RHom(K, Rf_* M) ≅
Rf_* RHom(f^* K, M)` of the adjunction.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [MonoidalClosed D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal]

/-- For an adjunction `F ⊣ G` with `F` strong monoidal, `[K, G Y] ≅ G [F K, Y]`, naturally in
`Y`: both sides are right adjoint to `Y ↦ F (K ⊗ Y) ≅ F K ⊗ F Y`, so they are identified by
uniqueness of right adjoints.
```
             K ⊗ -              F
        C ─────────────▶ C ─────────────▶ D
        C ◀───────────── C ◀───────────── D
             [K, -]             G

             F                F K ⊗ -
        C ─────────────▶ D ─────────────▶ D
        C ◀───────────── D ◀───────────── D
             G               [F K, -]
```
The two top rows are isomorphic (`Functor.Monoidal.commTensorLeft`), hence so are the composite
right adjoints `G ⋙ [K, -]` and `[F K, -] ⋙ G` of the bottom rows. -/
noncomputable def ihomCompIso (K : C) : G ⋙ ihom K ≅ ihom (F.obj K) ⋙ G :=
  ((ihom.adjunction K).comp adj).rightAdjointUniq
    ((adj.comp (ihom.adjunction (F.obj K))).ofNatIsoLeft (Functor.Monoidal.commTensorLeft F K))

end CategoryTheory.Adjunction
