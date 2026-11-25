/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.GaloisUnitsCohomology
import Mathlib.Tactic.Abel

/-!
# Explicit continuous two-cocycles with separable-closure unit coefficients

Source: Stacks Project, Etale Cohomology, Section 0DVG, inhomogeneous differential.
(blueprint: def-sc-galois-units-two-cocycle-classes).
-/

@[expose] public section

universe u

namespace Field

variable (K : Type u) [Field K]

/-- Continuous inhomogeneous two-cocycles for the absolute Galois action.
The displayed equation is exactly `d₂ c = 0`, written without a finite sum.
Source: Stacks Project, Section 0DVG, displayed inhomogeneous differential.
(blueprint: def-sc-galois-units-two-cocycle-classes). -/
def GaloisUnitsTwoCocycle : Type u :=
  { c : (Gal(SeparableClosure K/K) × Gal(SeparableClosure K/K)) →
      (galoisUnitsTopRep K) //
    Continuous c ∧ ∀ g h i,
      (galoisUnitsTopRep K).ρ g (c (h, i)) - c (g * h, i) +
        c (g, h * i) - c (g, h) = 0 }

/-- Two continuous cocycles differ by a continuous one-cochain coboundary.
Source: Stacks Project, Section 0DVG, the degree-one inhomogeneous differential.
(blueprint: def-sc-galois-units-two-cocycle-classes). -/
def galoisUnitsTwoCocycleRel (c d : GaloisUnitsTwoCocycle K) : Prop :=
  ∃ b : Gal(SeparableClosure K/K) → (galoisUnitsTopRep K),
    Continuous b ∧ ∀ g h,
      d.val (g, h) = c.val (g, h) +
        ((galoisUnitsTopRep K).ρ g (b h) - b (g * h) + b g)

/-- The continuous-coboundary relation is an equivalence relation. Negating a one-cochain
reverses a coboundary and adding two one-cochains composes coboundaries.
Source: Stacks Project, Section 0DVG.
(blueprint: def-sc-galois-units-two-cocycle-classes). -/
def galoisUnitsTwoCocycleSetoid : Setoid (GaloisUnitsTwoCocycle K) where
  r := galoisUnitsTwoCocycleRel K
  iseqv := {
    refl := by
      intro c
      refine ⟨fun _ ↦ 0, continuous_const, ?_⟩
      intro g h
      simp
    symm := by
      intro c d hcd
      obtain ⟨b, hb, hbd⟩ := hcd
      refine ⟨fun g ↦ -b g, hb.neg, ?_⟩
      intro g h
      rw [hbd g h]
      simp only [map_neg]
      abel
    trans := by
      intro c d e hcd hde
      obtain ⟨b, hb, hbd⟩ := hcd
      obtain ⟨a, ha, hae⟩ := hde
      refine ⟨fun g ↦ b g + a g, hb.add ha, ?_⟩
      intro g h
      rw [hae g h, hbd g h]
      simp only [map_add]
      abel }

/-- Continuous two-cocycles modulo continuous coboundaries. This explicit quotient uses
jointly continuous functions on `G × G` and the usual inhomogeneous differential; it does
not use etale sheaf cohomology or Mathlib's homogeneous continuous cohomology.
Source: Stacks Project, Section 0DVG.
(blueprint: def-sc-galois-units-two-cocycle-classes). -/
def GaloisUnitsTwoCocycleClasses : Type u := Quotient (galoisUnitsTwoCocycleSetoid K)

end Field
