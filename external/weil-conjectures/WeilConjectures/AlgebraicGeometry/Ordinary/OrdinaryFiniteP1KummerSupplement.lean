/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Kummer

/-!
# Canonical arrows for the ordinary finite projective-line calculation

## Main definitions

* `ordinaryFiniteRootMap`: scalar extension of roots of unity.
* `ordinaryFiniteClass`: realization of a module-derived class in abelian cohomology.
* `ordinaryFiniteP1KummerClass`: the scalar Kummer class of the specified `O(1)`.

## References

* Stacks Project, Tags 03PL and 03FD
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor ChangeOfRings

namespace AlgebraicGeometry.Etale

-- Reuse the proposition instances already stored in the ordinary derived category.
-- This keeps the canonical localization data identical before taking object maps.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] ModuleCat.extendScalars
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
  Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor

attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance

set_option backward.isDefEq.respectTransparency false in
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor

attribute [local irreducible] ordinaryFiniteExtHomEquiv

set_option backward.isDefEq.respectTransparency.types true in
private theorem realize_equiv_apply {U V W : Type*} (e : U ≃ V) (f : U → W) (x : U) :
    f (e.symm (e x)) = f x := congrArg f (e.symm_apply_apply x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarUnitComposite_naturality (R : Type) (S : Type (u + 1))
    [CommRing R] [CommRing S] (r : R →+* S)
    {M M' : ModuleCat.{u + 1} R} {P P' : ModuleCat.{u + 1} S}
    (f : M ⟶ M') (g : P ⟶ P')
    (s : (ModuleCat.extendScalars r).obj M ⟶ P)
    (s' : (ModuleCat.extendScalars r).obj M' ⟶ P')
    (h : (ModuleCat.extendScalars r).map f ≫ s' = s ≫ g) :
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map f ≫
        AddCommGrpCat.ofHom
          ((ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{0, u + 1, u + 1}
            r s').hom.toAddMonoidHom) =
      AddCommGrpCat.ofHom
        ((ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{0, u + 1, u + 1}
          r s).hom.toAddMonoidHom) ≫
        (forget₂ (ModuleCat.{u + 1} S) AddCommGrpCat.{u + 1}).map g := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} r
  have hh := congrArg (adj.homEquiv M P') h
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at hh
  apply AddCommGrpCat.ext
  intro x
  exact congrArg (fun k ↦ k x) hh

attribute [local irreducible]
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
  Scheme.finiteEtaleTwistScalar

attribute [local irreducible] ordinaryFiniteRootMap Sheaf.H.map

/-- The degree-zero object is concentrated in degrees at least zero. -/
instance ordinaryFiniteDegreeZero_isGE (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategory.TStructure.t.IsGE (ordinaryFiniteDegreeZero A T F) 0 :=
  by
    unfold ordinaryFiniteDegreeZero
    infer_instance

/-- The degree-zero object is concentrated in degrees at most zero. -/
instance ordinaryFiniteDegreeZero_isLE (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategory.TStructure.t.IsLE (ordinaryFiniteDegreeZero A T F) 0 :=
  by
    unfold ordinaryFiniteDegreeZero
    infer_instance

end AlgebraicGeometry.Etale
