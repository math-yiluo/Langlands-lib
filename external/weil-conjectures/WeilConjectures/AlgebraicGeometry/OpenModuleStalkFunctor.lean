/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Topology.Sheaves.Abelian

/-! # Stalks of module sheaves on the site over an open

Source: Stacks Project, Modules, Tag 01AG, and Cohomology of Sheaves, Tag 08C4.
(blueprint: def-sc-open-module-stalk-functor).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

/-- The stalk on the site over `U`, transported to the original stalk ring.
Source: Stacks Project, Modules, Tag 01AG; the open-subspace interpretation in
Cohomology of Sheaves, Tag 08C4.
(blueprint: def-sc-open-module-stalk-functor).

Convert sheaves on the slice site to sheaves on the open subscheme, take their
module stalk at the specified point, and restrict scalars along the open immersion's
stalk ring map. This is an explicit composite, with no choice of a model. -/
def openModuleStalkFunctor (Y : Scheme.{u}) (U : Y.Opens) (y : U.toScheme) :
    SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U) ⥤
      ModuleCat.{u} (Y.presheaf.stalk (U.ι y)) :=
  (Scheme.Modules.overEquiv U).functor ⋙
    RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace y ⋙
      ModuleCat.restrictScalars (U.ι.stalkMap y).hom

set_option backward.isDefEq.respectTransparency false in
/-- This stalk construction preserves zero maps, so it can be applied to complexes.
Source: Stacks Project, Modules, Tag 01AG.
(blueprint: def-sc-open-module-stalk-functor).
Proof: the site equivalence is additive because it preserves binary products;
the module stalk and restriction of scalars preserve zero maps. Compose these facts. -/
instance openModuleStalkFunctor_preservesZeroMorphisms
    (Y : Scheme.{u}) (U : Y.Opens) (y : U.toScheme) :
    (openModuleStalkFunctor Y U y).PreservesZeroMorphisms := by
  let A := (Scheme.Modules.overEquiv U).functor
  have : A.Additive := Functor.additive_of_preserves_binary_products _
  have : A.PreservesZeroMorphisms := inferInstance
  have : (RingedSpace.moduleStalkFunctor
      U.toScheme.toRingedSpace y).PreservesZeroMorphisms :=
    RingedSpace.moduleStalkFunctor_preservesZeroMorphisms _ _
  have : (ModuleCat.restrictScalars (U.ι.stalkMap y).hom).PreservesZeroMorphisms :=
    inferInstance
  change (A ⋙ RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace y ⋙
    ModuleCat.restrictScalars (U.ι.stalkMap y).hom).PreservesZeroMorphisms
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_exact (X : RingedSpace.{u}) (x : X) :
    PreservesFiniteLimits (RingedSpace.moduleStalkFunctor X x) ∧
      PreservesFiniteColimits (RingedSpace.moduleStalkFunctor X x) := by
  let A : ModuleCat.{u} (X.presheaf.stalk x) ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} (moduleRings X)) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful (moduleRings X)).2.2.1
  have : PreservesFiniteLimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := inferInstance
  have : PreservesFiniteColimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := inferInstance
  have : PreservesFiniteLimits (RingedSpace.moduleStalkFunctor X x ⋙ A) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf (moduleRings X) ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)))
  have : PreservesFiniteColimits (RingedSpace.moduleStalkFunctor X x ⋙ A) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf (moduleRings X) ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ A,
    preservesFiniteColimits_of_reflects_of_preserves _ A⟩

set_option backward.isDefEq.respectTransparency false in
/-- The localized module stalk functor preserves finite limits.
Source: Stacks Project, Modules, Tag 01AG.
(blueprint: def-sc-open-module-stalk-functor).
Proof: reflect finite limits through forgetting the stalk module structure;
then compose with the site equivalence and restriction of scalars. -/
instance openModuleStalkFunctor_preservesFiniteLimits
    (Y : Scheme.{u}) (U : Y.Opens) (y : U.toScheme) :
    PreservesFiniteLimits (openModuleStalkFunctor Y U y) := by
  have := (stalk_exact U.toScheme.toRingedSpace y).1
  dsimp [openModuleStalkFunctor]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The localized module stalk functor preserves finite colimits.
Source: Stacks Project, Modules, Tag 01AG.
(blueprint: def-sc-open-module-stalk-functor).
Proof: reflect finite colimits through forgetting the stalk module structure;
then compose with the site equivalence and restriction of scalars. -/
instance openModuleStalkFunctor_preservesFiniteColimits
    (Y : Scheme.{u}) (U : Y.Opens) (y : U.toScheme) :
    PreservesFiniteColimits (openModuleStalkFunctor Y U y) := by
  have := (stalk_exact U.toScheme.toRingedSpace y).2
  dsimp [openModuleStalkFunctor]
  infer_instance

/-- The localized module stalk functor is additive.
Source: Stacks Project, Modules, Tag 01AG.
(blueprint: def-sc-open-module-stalk-functor).
Proof: preservation of finite limits gives preservation of binary products,
which implies additivity for functors between additive categories. -/
instance openModuleStalkFunctor_additive
    (Y : Scheme.{u}) (U : Y.Opens) (y : U.toScheme) :
    (openModuleStalkFunctor Y U y).Additive :=
  Functor.additive_of_preserves_binary_products _

end
end AlgebraicGeometry
