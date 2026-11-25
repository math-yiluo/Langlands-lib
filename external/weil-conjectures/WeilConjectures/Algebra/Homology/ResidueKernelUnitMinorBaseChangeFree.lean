/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.Stability
@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace ModuleCat
set_option backward.dsimp.instances true in
/--
(blueprint: new-residue-kernel-unit-minor-base-change-free)
Finite projective modules remain free after localization at a prime.
Source: Stacks Project, Tags 00NX and 00O0. Finite projectivity gives flatness,
and finite flat modules over the local ring A are free. -/
theorem residue_kernel_unit_minor_base_change_free
    (R : Type v) [CommRing R] (X Y : ModuleCat.{v} R)
    (hfX : Module.Finite R X) (hfY : Module.Finite R Y)
    (hpX : Module.Projective R X) (hpY : Module.Projective R Y)
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    Module.Free (Localization.AtPrime 𝔭)
      ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).obj X) ∧
    Module.Free (Localization.AtPrime 𝔭)
      ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).obj Y) := by
  let := hfX
  let := hfY
  let := hpX
  let := hpY
  constructor
  · dsimp [extendScalars, ExtendScalars.obj', restrictScalars, RestrictScalars.obj']
    let : Algebra R (Localization.AtPrime 𝔭) :=
      (algebraMap R (Localization.AtPrime 𝔭)).toAlgebra
    exact Module.free_of_flat_of_isLocalRing
  · dsimp [extendScalars, ExtendScalars.obj', restrictScalars, RestrictScalars.obj']
    let : Algebra R (Localization.AtPrime 𝔭) :=
      (algebraMap R (Localization.AtPrime 𝔭)).toAlgebra
    exact Module.free_of_flat_of_isLocalRing
end ModuleCat
