/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.FlatModuleCanonicalDerivedPullbackAux
import WeilConjectures.AlgebraicGeometry.IntrinsicFlatModuleTensorFlat

/-! # The canonical derived pullback comparison at a flat module

Source: Stacks Project, Tags 06YD and 06YJ.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- A canonical derived-to-ordinary pullback comparison at a quasi-coherent module
flat over its own scheme is invertible. The affine-local IsFlatOver predicate at the
identity expresses intrinsic flatness, independently of any family morphism.

Source: Stacks Project, Tags 06YD and 06YJ;
`lemma-coherent-base-change-invertible-sheaves--2`, Steps 1--2.
(blueprint: lem-pc-flat-module-canonical-derived-pullback).

Proof: On an affine open, intrinsic flatness says that the section module is flat
over the coordinate ring. Localizing proves stalkwise flatness, which for a
quasi-coherent sheaf is equivalent to exactness of tensoring with it. Thus G[0] is a
bounded-above termwise flat complex (the other terms are zero). Apply
flatComplexDerivedPullback to compute its derived pullback by termwise tensor
pullback. Identify the functor F in that theorem with tensorPullback using its
specified equalities on objects and maps. The resulting counit is invertible at
G[0]. Any other left-derived counit for the same functor differs by the unique
invertible comparison supplied by the left-derived universal property, so its
component there is also invertible. Unpack IsDerivedModulePullbackComparison:
c is precisely that component followed by the localization of the single-complex
pullback isomorphism. Both factors are invertible, so c is invertible. This applies
to arbitrary a, including maps with empty domain and the zero module. -/
theorem isIso_modulePullbackComparison_of_isFlatOver_identity
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (a : X ⟶ Y) [(Scheme.Modules.tensorPullback a).Additive]
    (G : Y.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : Scheme.Modules.IsFlatOver G (𝟙 Y))
    (c : (derivedPullback a).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback a).obj G))
    (hc : IsDerivedModulePullbackComparison a G c) : IsIso c := by
  obtain ⟨ε, hε, hc⟩ := hc
  rw [hc]
  have := isIso_flat_single_derived_counit a G
    (isFlat_of_isFlatOver_identity G hflat) ε hε
  change IsIso (ε.app ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj G) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback a) (ComplexShape.up ℤ) 0).hom.app G)))
  infer_instance

end AlgebraicGeometry
