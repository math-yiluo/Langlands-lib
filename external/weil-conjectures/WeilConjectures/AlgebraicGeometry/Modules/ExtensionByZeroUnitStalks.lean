/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroOutside
import WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroInside

/-! # A component of extension by zero for modules

## References

* Stacks Project, Sheaves, Lemma 00A7
* Stacks Project, Sheaves, Lemma 00A7 (3), after Lemma 00A3
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- The unit of any extension-by-zero adjunction gives the stalk identifications. -/
theorem module_extensionByZero_unit_stalks (X : Scheme.{u}) (U : X.Opens) :
    let R := X.ringCatSheaf
    let P := SheafOfModules.extensionByZeroPresheaf.{u} R U
    let L := P ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
    ∀ adj : L ⊣ SheafOfModules.overFunctor R U,
        (∀ (F : SheafOfModules.{u} (R.over U)) (x : X), x ∉ U →
          IsZero (TopCat.Presheaf.stalk (L.obj F).val.presheaf x)) ∧
        let t : ∀ (F : SheafOfModules.{u} (R.over U)) (x : U),
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
                ((toPresheaf U.toScheme).obj ((overEquiv U).functor.obj F)) ⟶
              (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
                (U.ι x)).obj (L.obj F) := fun F x =>
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              ((toPresheaf U.toScheme).map ((overEquiv U).functor.map (adj.unit.app F) ≫
                (overFunctorEquiv U).hom.app (L.obj F))) ≫
            (restrictStalkNatIso U.ι x).hom.app (L.obj F)
        (∀ (F : SheafOfModules.{u} (R.over U)) (x : U),
          letI : Module (U.toScheme.presheaf.stalk x)
              (((overEquiv U).functor.obj F).presheaf.stalk x) :=
            inferInstanceAs (Module (U.toScheme.presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk ((overEquiv U).functor.obj F).val.presheaf x))
          letI : Module (X.presheaf.stalk (U.ι x))
              ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
                (U.ι x)).obj (L.obj F)) :=
            inferInstanceAs (Module (X.presheaf.stalk (U.ι x))
            ↑(TopCat.Presheaf.stalk (L.obj F).val.presheaf (U.ι x)))
          IsIso (t F x) ∧
            ∀ (r : X.presheaf.stalk (U.ι x))
              (s : ((overEquiv U).functor.obj F).presheaf.stalk x),
              t F x ((U.ι.stalkMap x) r • s) = r • t F x s) ∧
        (∀ (F F' : SheafOfModules.{u} (R.over U)) (α : F ⟶ F') (x : U),
          t F x ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι x)).map
              ((toPresheaf X).map (L.map α)) =
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              ((toPresheaf U.toScheme).map ((overEquiv U).functor.map α)) ≫ t F' x)   := by
  dsimp
  intro adj
  exact ⟨module_extensionByZero_outside_stalk X U,
    module_extensionByZero_inside_stalk X U adj⟩

end AlgebraicGeometry.Scheme.Modules
