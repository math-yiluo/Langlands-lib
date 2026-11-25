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

import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroHomFormula
import WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroUnitStalks

/-!
# Extension by zero of modules on an open subscheme

## References

* Stacks Project, Definition 00A4 and Lemma 00A7
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- Extension by zero is additive, left adjoint to restriction, and has the stated stalk properties.
-/
theorem module_extensionByZero_adjunction (X : Scheme.{u}) (U : X.Opens) :
    let R := X.ringCatSheaf
    let P := SheafOfModules.extensionByZeroPresheaf.{u} R U
    let L := P ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
    L.Additive ∧
      ∃ adj : L ⊣ SheafOfModules.overFunctor R U,
        (∀ (F : SheafOfModules.{u} (R.over U)) (G : X.Modules)
          (ψ : L.obj F ⟶ G) (V : X.Opens) (h : V ⟶ U)
          (s : F.val.obj (op (Over.mk h))),
          ((adj.homEquiv F G ψ).val.app (op (Over.mk h))) s =
            (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) ψ).app (op V)
              (DirectSum.of (fun φ : V ⟶ U => F.val.obj (op (Over.mk φ))) h s)) ∧
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
              ((toPresheaf U.toScheme).map ((overEquiv U).functor.map α)) ≫ t F' x) := by
  dsimp
  let L := SheafOfModules.extensionByZeroPresheaf.{u} X.ringCatSheaf U ⋙
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have : PreservesFiniteLimits L :=
    (open_restriction_adjunction_exact (X.toRingedSpace) U).2.2.1
  have : PreservesLimit (Functor.empty.{0} _) L := inferInstance
  have : L.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  have hadd : L.Additive := Functor.additive_of_preserves_binary_products L
  obtain ⟨adj, hformula⟩ := module_extensionByZero_hom_formula X U
  exact ⟨hadd, adj, hformula, module_extensionByZero_unit_stalks X U adj⟩

end AlgebraicGeometry.Scheme.Modules
