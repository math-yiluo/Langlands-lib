/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-! # Fibers of the filtered arrow colimit

Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph.
(blueprint: def-weil-pbc-filtered-colimit-hom-fibers).
-/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {J : Type z} [SmallCategory J] (F : J ⥤ Cat.{z, z})

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph.
(blueprint: def-weil-pbc-filtered-colimit-hom-fibers).
The source map descended from the source maps of the stage categories. -/
noncomputable def filteredColimitArrowSource :
    colimit (F ⋙ Cat.arrows) → colimit (F ⋙ Cat.objects) :=
  colimit.desc (F ⋙ Cat.arrows)
    { pt := colimit (F ⋙ Cat.objects)
      ι :=
        { app := fun j ↦ TypeCat.ofHom (fun a ↦ colimit.ι (F ⋙ Cat.objects) j a.left)
          naturality := by
            intro j k f
            ext a
            exact ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.objects) f) a.left } }

/-- Target map descended from the target maps of the stage categories. 
(blueprint: def-weil-pbc-filtered-colimit-hom-fibers)
-/
noncomputable def filteredColimitArrowTarget :
    colimit (F ⋙ Cat.arrows) → colimit (F ⋙ Cat.objects) :=
  colimit.desc (F ⋙ Cat.arrows)
    { pt := colimit (F ⋙ Cat.objects)
      ι :=
        { app := fun j ↦ TypeCat.ofHom (fun a ↦ colimit.ι (F ⋙ Cat.objects) j a.right)
          naturality := by
            intro j k f
            ext a
            exact ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.objects) f) a.right } }

/-- (blueprint: def-weil-pbc-filtered-colimit-hom-fibers) -/
@[simp] theorem filteredColimitArrowSource_ι (j : J) (a : Arrow (F.obj j)) :
    filteredColimitArrowSource F (colimit.ι (F ⋙ Cat.arrows) j a) =
      colimit.ι (F ⋙ Cat.objects) j a.left := by
  unfold filteredColimitArrowSource
  exact ConcreteCategory.congr_hom (colimit.ι_desc (F := F ⋙ Cat.arrows) _ j) a

/-- (blueprint: def-weil-pbc-filtered-colimit-hom-fibers) -/
@[simp] theorem filteredColimitArrowTarget_ι (j : J) (a : Arrow (F.obj j)) :
    filteredColimitArrowTarget F (colimit.ι (F ⋙ Cat.arrows) j a) =
      colimit.ι (F ⋙ Cat.objects) j a.right := by
  unfold filteredColimitArrowTarget
  exact ConcreteCategory.congr_hom (colimit.ι_desc (F := F ⋙ Cat.arrows) _ j) a

/-- The arrows in the set colimit with prescribed source and target. 
(blueprint: def-weil-pbc-filtered-colimit-hom-fibers)
-/
def FilteredColimitHom (X Y : colimit (F ⋙ Cat.objects)) :=
  { a : colimit (F ⋙ Cat.arrows) //
    filteredColimitArrowSource F a = X ∧ filteredColimitArrowTarget F a = Y }

/-- A stage morphism viewed in the corresponding fiber of the arrow colimit. 
(blueprint: def-weil-pbc-filtered-colimit-hom-fibers)
-/
noncomputable def filteredColimitHomι (j : J) {X Y : F.obj j} (f : X ⟶ Y) :
    FilteredColimitHom F (colimit.ι (F ⋙ Cat.objects) j X)
      (colimit.ι (F ⋙ Cat.objects) j Y) :=
  ⟨colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk f),
    filteredColimitArrowSource_ι F j (Arrow.mk f),
    filteredColimitArrowTarget_ι F j (Arrow.mk f)⟩


end CategoryTheory
