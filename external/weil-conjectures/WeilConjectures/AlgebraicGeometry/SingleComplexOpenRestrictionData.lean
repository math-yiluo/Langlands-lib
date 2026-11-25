/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Canonical open pullback and restricted coefficient data

Source: Stacks Project, Tag 0DJ9, first paragraph; Tag 08HY, counit description.
(blueprint: def-pc-single-complex-open-restriction-data).

These are the unchanged constructions formerly in SingleComplexOpenRestrictionComparison.
They are isolated here so independent compatibility calculations can import them without a cycle.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison from pullback along an open immersion to exact restriction,
constructed using the pinned tensor-pullback adjunction and left-derived counit.
Source: Stacks Project, Tag 08DW, restriction of derived pullback.
(blueprint: lem-pc-single-complex-open-restriction-comparison).
(blueprint: def-pc-single-complex-open-restriction-data)
-/
noncomputable def singleComplexOpenPullbackIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (Y : Scheme.{u}) (U : Y.Opens) :
    derivedPullback U.ι ≅ (schemeOpenRestriction Y U).mapDerivedCategory := by
  classical
  let T : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback U.ι
  have : T.Additive := (Classical.choose exists_derivedPullbackComposition) U.ι
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) U.ι
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  have : (derivedPullback U.ι).IsLeftDerivedFunctor ε W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) U.ι
  let η : T ≅ Scheme.Modules.restrictFunctor U.ι :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.ι)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
  let θ : schemeOpenRestriction Y U ≅ T := Scheme.Modules.overFunctorEquiv U ≪≫ η.symm
  have : PreservesFiniteLimits (schemeOpenRestriction Y U) :=
    schemeOpenRestriction_preservesFiniteLimits Y U
  have : PreservesFiniteColimits (schemeOpenRestriction Y U) :=
    schemeOpenRestriction_preservesFiniteColimits Y U
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso θ
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso θ
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  exact Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback U.ι) ε
    T.mapDerivedCategoryFactorsh.hom W ≪≫ (Functor.mapDerivedCategoryNatIso θ).symm

/-- Restrict the coefficient morphism using the canonical pullback composition
comparisons and the constructed open-pullback comparisons. Both objects and the
morphism are constructed; no existence theorem supplies arbitrary coefficient data.
Source: Stacks Project, Tag 0DJ9, first paragraph.
(blueprint: lem-pc-single-complex-open-restriction-comparison).
(blueprint: def-pc-single-complex-open-restriction-data)
-/
noncomputable def singleComplexRestrictedCoefficient
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ g') :
    (derivedPullback j).obj ((schemeOpenRestriction X U).mapDerivedCategory.obj K) ⟶
      (schemeOpenRestriction X' U').mapDerivedCategory.obj K' :=
  (derivedPullback j).map ((singleComplexOpenPullbackIso X U).inv.app K) ≫
  ((Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) j U.ι).hom.app K ≫
  eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hj) ≫
  ((Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) U'.ι g').inv.app K ≫
  (singleComplexOpenPullbackIso X' U').hom.app ((derivedPullback g').obj K) ≫
  (schemeOpenRestriction X' U').mapDerivedCategory.map φ

end AlgebraicGeometry
