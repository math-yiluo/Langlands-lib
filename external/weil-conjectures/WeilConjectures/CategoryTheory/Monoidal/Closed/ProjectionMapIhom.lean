/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.IhomUnitTensor

/-!
# Internal homs out of a left adjoint with invertible projection maps

For adjunctions `L ⊣ G ⊣ R` between braided monoidal closed categories with `G` monoidal, if the
projection maps `L (G A ⊗ M) ⟶ A ⊗ L M` (`CategoryTheory.Functor.Monoidal.projectionMap`) are
invertible for all `A`, then `[L M, N] ≅ R [M, G N]` naturally in `N`.

## Main definitions

- `CategoryTheory.Functor.Monoidal.tensorLeftIsoOfIsIsoProjectionMap`:
  `G ⋙ tensorLeft M ⋙ L ≅ tensorLeft (L.obj M)`.
- `CategoryTheory.Functor.Monoidal.ihomObjIsoOfIsIsoProjectionMap`:
  `ihom (L.obj M) ≅ G ⋙ ihom M ⋙ R`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Functor.Monoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D] [MonoidalClosed C] [MonoidalClosed D]
  {G : C ⥤ D} [G.Monoidal] {L R : D ⥤ C} (adj : L ⊣ G) (adj' : G ⊣ R)

/-- If the projection maps `L (G A ⊗ M) ⟶ A ⊗ L M` are invertible for all `A`, then
`T ↦ L (M ⊗ G T)` is isomorphic to `T ↦ L M ⊗ T`, through the braidings. -/
noncomputable def tensorLeftIsoOfIsIsoProjectionMap (M : D)
    [∀ A, IsIso ((projectionMap adj A).app M)] :
    G ⋙ tensorLeft M ⋙ L ≅ tensorLeft (L.obj M) :=
  NatIso.ofComponents
    (fun A ↦ L.mapIso (β_ M (G.obj A)) ≪≫ asIso ((projectionMap adj A).app M) ≪≫
      β_ A (L.obj M))
    fun {A A'} g ↦ by
      dsimp
      rw [← L.map_comp_assoc, BraidedCategory.braiding_naturality_right, L.map_comp_assoc,
        projectionMap_naturality_left_assoc, BraidedCategory.braiding_naturality_left]
      simp

/-- For adjunctions `L ⊣ G ⊣ R` with `G` monoidal, if the projection maps
`L (G A ⊗ M) ⟶ A ⊗ L M` are invertible for all `A`, then `[L M, N] ≅ R [M, G N]`, naturally in
`N`: both are right adjoint to `T ↦ L M ⊗ T ≅ L (M ⊗ G T)`. -/
noncomputable def ihomObjIsoOfIsIsoProjectionMap (M : D)
    [∀ A, IsIso ((projectionMap adj A).app M)] :
    ihom (L.obj M) ≅ G ⋙ ihom M ⋙ R :=
  (ihom.adjunction (L.obj M)).rightAdjointUniq
    (((adj'.comp (ihom.adjunction M)).comp adj).ofNatIsoLeft
      (tensorLeftIsoOfIsIsoProjectionMap adj M))


end CategoryTheory.Functor.Monoidal
