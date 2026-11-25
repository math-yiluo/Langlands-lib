/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.IsTensorProduct

/-! # Extension of scalars along a pushout square of commutative rings

For a pushout square of commutative rings `A → B → D`, `A → C → D` and a `C`-module `M`,
`B ⊗_A M ≅ D ⊗_C M` as `B`-modules, sending `b ⊗ m` to `p b ⊗ m`
(`ModuleCat.exists_extendScalars_restrictScalars_iso_of_isPushout`).
Source: Stacks Project, Tag 00DE.
-/

@[expose] public section

universe r

open CategoryTheory Limits

open scoped TensorProduct ChangeOfRings

namespace ModuleCat

/-- Base change along a pushout square of commutative rings: for a module `M` over `C`,
`B ⊗_A M ≅ D ⊗_C M`, sending `b ⊗ m` to `p b ⊗ m`.
Source: Stacks Project, Tag 00DE (tensor cancellation). -/
theorem exists_extendScalars_restrictScalars_iso_of_isPushout
    {A B C D : CommRingCat.{r}}
    (f : A ⟶ B) (g : A ⟶ C) (p : B ⟶ D) (q : C ⟶ D)
    (h : IsPushout f g p q) (M : ModuleCat.{r} C) :
    ∃ e : (ModuleCat.extendScalars f.hom).obj
        ((ModuleCat.restrictScalars g.hom).obj M) ≅
      (ModuleCat.restrictScalars p.hom).obj ((ModuleCat.extendScalars q.hom).obj M),
      ∀ (b : B) (m : M), e.hom (b ⊗ₜ[A, f.hom] m) = p b ⊗ₜ[C, q.hom] m := by
  let : Algebra A B := f.hom.toAlgebra
  let : Algebra A C := g.hom.toAlgebra
  let : Algebra B D := p.hom.toAlgebra
  let : Algebra C D := q.hom.toAlgebra
  let : Algebra A D := (q.hom.comp g.hom).toAlgebra
  have hc : p.hom.comp f.hom = q.hom.comp g.hom :=
    congrArg CommRingCat.Hom.hom h.w
  have : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' hc.symm
  have : Algebra.IsPushout A B C D := CommRingCat.isPushout_iff_isPushout.mp h
  let : Module A M := Module.compHom M g.hom
  have : IsScalarTower A C M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact ⟨(Algebra.IsPushout.cancelBaseChange A B C D M).symm.toModuleIso,
    fun b m ↦ Algebra.IsPushout.cancelBaseChange_symm_tmul A B C D M b m⟩

end ModuleCat
