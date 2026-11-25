/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Tactic.Algebraize

/-!
# Extension of scalars of finite and of flat modules

For a ring morphism `φ : R →+* S`, extension of scalars `M ↦ S ⊗_R M`
(`ModuleCat.extendScalars φ`) sends finite `R`-modules to finite `S`-modules
(`ModuleCat.finite_extendScalars_obj'`) and flat `R`-modules to flat `S`-modules
(`ModuleCat.flat_extendScalars_obj`).
-/

@[expose] public section

universe v u₁ u₂

namespace ModuleCat

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Extension of scalars of a finite module is finite. -/
lemma finite_extendScalars_obj' (M : ModuleCat.{v} R) [Module.Finite R M] :
    Module.Finite S ((extendScalars.{u₁, u₂, v} φ).obj M) := by
  algebraize [φ]
  have : Module.Finite S (TensorProduct R S M) := inferInstance
  exact this

/-- Extension of scalars of a flat module is flat. -/
lemma flat_extendScalars_obj (M : ModuleCat.{v} R) [Module.Flat R M] :
    Module.Flat S ((extendScalars.{u₁, u₂, v} φ).obj M) := by
  algebraize [φ]
  have : Module.Flat S (TensorProduct R S M) := inferInstance
  exact this

end ModuleCat
