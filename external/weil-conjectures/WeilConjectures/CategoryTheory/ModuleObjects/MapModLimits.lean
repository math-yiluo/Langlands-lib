/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-!
# Transport of module objects preserves limits

Let `F : C ⥤ D` be a lax monoidal functor and `R : C` a monoid object. Since the forgetful
functors from module objects create limits (`CategoryTheory.Mod.createsLimit`) and preserve them
(being right adjoints, `CategoryTheory.Mod.freeForgetAdjunction`), and
`F.mapMod R ⋙ Mod.forget (F.obj R) = Mod.forget R ⋙ F`, the functor
`F.mapMod R : Mod C R ⥤ Mod D (F.obj R)` preserves the limits that `F` preserves
(`CategoryTheory.Functor.preservesLimitsOfShape_mapMod`).
-/

@[expose] public section

namespace CategoryTheory

open Limits

open scoped CategoryTheory.Obj

variable {C : Type*} [Category* C] [MonoidalCategory C] {D : Type*} [Category* D]
  [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal] (R : C) [MonObj R]

namespace Functor

/-- If `F` preserves limits of shape `J`, then so does the transport `F.mapMod R` of module
objects: limits of module objects are computed on the underlying objects. -/
instance preservesLimitsOfShape_mapMod (J : Type*) [Category* J] [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J (F.mapMod R) :=
  have := (Mod.freeForgetAdjunction R).rightAdjoint_preservesLimits
  have : PreservesLimitsOfShape J (F.mapMod R ⋙ Mod.forget (F.obj R)) :=
    inferInstanceAs (PreservesLimitsOfShape J (Mod.forget R ⋙ F))
  preservesLimitsOfShape_of_reflects_of_preserves (F.mapMod R) (Mod.forget (F.obj R))

/-- If `F` preserves limits of size `(w, w')`, then so does the transport `F.mapMod R` of module
objects. -/
instance preservesLimitsOfSize_mapMod [PreservesLimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} (F.mapMod R) where
  preservesLimitsOfShape := inferInstance

end Functor

end CategoryTheory
