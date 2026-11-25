/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Objects sent to the unit by a monoidal functor

Let `F : C ⥤ D` be a strong monoidal functor. If `F` sends `X` and `Y` to objects isomorphic to
the unit `𝟙_ D`, then so it does with `X ⊗ Y` (`CategoryTheory.Functor.mapTensorObjIsoUnit`)
and, if `F` commutes with the internal homs out of `X`, with the internal hom `[X, Y]`
(`CategoryTheory.Functor.mapIhomObjIsoUnit`). This is used to show that tensor powers and duals
of a locally trivial invertible sheaf are locally trivial.
-/

@[expose] public section

namespace CategoryTheory.Functor

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- A monoidal functor sends the unit to the unit. -/
noncomputable def mapUnitIsoUnit : F.obj (𝟙_ C) ≅ 𝟙_ D :=
  (Monoidal.εIso F).symm

/-- If a monoidal functor sends `X` and `Y` to the unit, it sends `X ⊗ Y` to the unit. -/
noncomputable def mapTensorObjIsoUnit {X Y : C} (e : F.obj X ≅ 𝟙_ D) (e' : F.obj Y ≅ 𝟙_ D) :
    F.obj (X ⊗ Y) ≅ 𝟙_ D :=
  (Monoidal.μIso F X Y).symm ≪≫ (e ⊗ᵢ e') ≪≫ λ_ (𝟙_ D)

/-- If a monoidal functor sends `X` and `Y` to the unit and commutes with the internal homs out
of `X`, it sends the internal hom `[X, Y]` to the unit: `F [X, Y] ≅ [F X, F Y] ≅ [𝟙, 𝟙] ≅ 𝟙`. -/
noncomputable def mapIhomObjIsoUnit [MonoidalClosed C] [MonoidalClosed D] {X Y : C}
    [IsIso (LaxMonoidal.ihomComparison F X)] (e : F.obj X ≅ 𝟙_ D)
    (e' : F.obj Y ≅ 𝟙_ D) :
    F.obj ((ihom X).obj Y) ≅ 𝟙_ D :=
  asIso ((LaxMonoidal.ihomComparison F X).app Y) ≪≫ (ihom (F.obj X)).mapIso e' ≪≫
    ((MonoidalClosed.internalHom.mapIso e.op).app (𝟙_ D)).symm ≪≫
    (MonoidalClosed.unitNatIso.app (𝟙_ D)).symm

end CategoryTheory.Functor
