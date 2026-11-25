/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# The underlying abelian sheaf of a constant sheaf of modules

For a scheme `T`, a commutative ring `R` and an `R`-module `M`, the underlying abelian sheaf
of the constant sheaf of `R`-modules with value `M` on the small étale site of `T` is the
constant abelian sheaf with value the underlying abelian group of `M`, naturally in `M` and
compatibly with the canonical maps from the constant presheaf. This is Mathlib's
`CategoryTheory.constantCommuteCompose` for the forgetful functor
`ModuleCat R ⥤ AddCommGrpCat`, which preserves sheafification.

## References

* Stacks Project, Tag 03CY
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) (R : Type (u + 1)) [CommRing R]

/-- The forgetful functor from sheaves of `R`-modules to abelian sheaves commutes with the
constant-sheaf functors on the small étale site: the underlying abelian sheaf of the constant
sheaf of `R`-modules with value `M` is the constant abelian sheaf with value `M`, naturally
in `M`. -/
noncomputable def constantModuleSheafForgetIso :
    constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙
        sheafCompose T.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) ≅
      forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ⋙
        constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  have : T.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  constantCommuteCompose T.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})

/-- The comparison `constantModuleSheafForgetIso` is compatible with the canonical maps from
the constant presheaf `U ↦ M`: the underlying abelian map of the module sheafification unit,
followed by the comparison, is the abelian sheafification unit of the constant presheaf. -/
theorem whiskerRight_toSheafify_constantModuleSheafForgetIso_hom (M : ModuleCat.{u + 1} R) :
    Functor.whiskerRight (toSheafify T.smallEtaleTopology ((Functor.const _).obj M))
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) ≫
      ((constantModuleSheafForgetIso T R).hom.app M).hom =
    (Functor.constComp _ M (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).hom ≫
      toSheafify T.smallEtaleTopology
        ((Functor.const _).obj ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj M)) := by
  have : T.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  rw [constantModuleSheafForgetIso, constantCommuteCompose_hom_app_hom,
    sheafComposeIso_inv_fac_assoc, toSheafify_naturality]

end AlgebraicGeometry.Scheme
