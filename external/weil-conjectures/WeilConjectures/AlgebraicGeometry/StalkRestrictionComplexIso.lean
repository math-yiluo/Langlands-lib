/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Canonical comparison of restriction followed by stalk pullback

Source: finite matrix extension argument, comparison step, in
lem-pc-finite-free-stalk-chain-map-pair-lift.
(blueprint: def-pc-stalk-restriction-complex-iso)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical comparison between stalk pullback after restriction and stalk pullback.

Source: lem-pc-finite-free-stalk-chain-map-pair-lift, proof step 3; Mathlib's
`restrictFunctorIsoPullback`, `pullbackComp`, and `Opens.fromSpecStalkOfMem_ι`.
First replace restriction by pullback along the open inclusion, then compose the
pullbacks, and finally use the equality of the composite scheme morphism with
`Y.fromSpecStalk y`. Apply this natural isomorphism termwise to complexes.
(blueprint: def-pc-stalk-restriction-complex-iso) -/
noncomputable def stalkRestrictionComplexIso {Y : Scheme.{u}} (V : Y.Opens)
    (y : Y) (hyV : y ∈ V) :
    (restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      (Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ) ≅
      (Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
    (Functor.isoWhiskerRight (restrictFunctorIsoPullback V.ι)
        (Modules.pullback (V.fromSpecStalkOfMem y hyV)) ≪≫
      pullbackComp (V.fromSpecStalkOfMem y hyV) V.ι ≪≫
      pullbackCongr (V.fromSpecStalkOfMem_ι y hyV)) (ComplexShape.up ℤ)

end AlgebraicGeometry.Scheme.Modules
