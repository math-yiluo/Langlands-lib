/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-! # Conservative functors preserving equalizers are faithful -/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- A conservative functor preserving equalizers is faithful.

Source: the equalizer criterion for equality of morphisms, used for descent on the
Artin–Schreier cover (blueprint: lem-kernel-conservative-left-exact-faithful).

Proof. When the images of two arrows coincide, the image of their equalizer inclusion
is invertible, since preservation identifies it with the equalizer inclusion of equal
arrows. Conservativity makes the original inclusion invertible. Cancel its epimorphism
property in the equalizer equation. -/
theorem faithful_of_preservesEqualizers_of_reflectsIsomorphisms
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasEqualizers C] [HasEqualizers D] (F : C ⥤ D)
    [PreservesLimitsOfShape WalkingParallelPair F] [F.ReflectsIsomorphisms] : F.Faithful where
  map_injective {X Y} f g h := by
    have : IsIso (equalizer.ι (F.map f) (F.map g)) := equalizer.ι_of_eq h
    have : IsIso (F.map (equalizer.ι f g)) := by
      have he : F.map (equalizer.ι f g) =
          (PreservesEqualizer.iso F f g).hom ≫ equalizer.ι (F.map f) (F.map g) := by
        rw [← PreservesEqualizer.iso_inv_ι F f g, Iso.hom_inv_id_assoc]
      rw [he]
      infer_instance
    have : IsIso (equalizer.ι f g) := isIso_of_reflects_iso _ F
    exact (cancel_epi (equalizer.ι f g)).1 (equalizer.condition f g)

end CategoryTheory.Functor
