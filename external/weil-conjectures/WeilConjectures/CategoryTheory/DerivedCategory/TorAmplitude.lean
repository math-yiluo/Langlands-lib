/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!

# Tor amplitude in a monoidal derived category

Let `C` be a monoidal closed braided Grothendieck abelian category, for instance a category of
sheaves of modules, such that the localization `Qh : K(C) ⥤ D(C)` admits a derived monoidal
structure (`Qh.HasDerivedMonoidalCategory`). Then `D(C)` carries the derived tensor product
`- ⊗ᴸ -` (`DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory`). This file defines
Tor amplitude for objects of `D(C)` with respect to this derived tensor product, tested by
tensoring with objects of `C` placed in degree `0`. The monoidal structure is not a parameter:
Tor amplitude only has its meaning for the derived tensor product.

Nothing here depends on a site: the étale and pro-étale Tor amplitude of
`WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude` are specialisations.

## Main definitions

- `DerivedCategory.torAmplitudeIn`: Tor amplitude in `[a, b]`.
- `DerivedCategory.finiteTorAmplitude`: finite Tor amplitude.

## Main results

- `DerivedCategory.exists_inf_homologyConcentratedIn_inf_torAmplitudeIn_iff`: for a property
  `P` of bounded objects, an object satisfies `P` and has finite Tor amplitude exactly when,
  for some interval `[a, b]`, it satisfies `P`, has homology concentrated in `[a, b]` and has
  Tor amplitude in `[a, b]`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [BraidedCategory C]

local instance instHasColimitsOfSize_torAmplitude
    : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- An object `M` of `D(C)` has *Tor amplitude in `[a, b]`* if for every object `F` of `C` the
derived tensor product `M ⊗ᴸ F` has homology concentrated in `[a, b]` (Stacks, Tag 0651). -/
def torAmplitudeIn (a b : ℤ) : ObjectProperty (DerivedCategory C) :=
  fun M ↦ ∀ F : C, homologyConcentratedIn a b (M ⊗ (singleFunctor C 0).obj F)

variable {C}

/-- Widening the interval preserves Tor amplitude. -/
lemma torAmplitudeIn.mono {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') {M : DerivedCategory C}
    (hM : torAmplitudeIn C a b M) : torAmplitudeIn C a' b' M :=
  fun F ↦ (hM F).mono ha hb

/-- Tor amplitude is invariant under isomorphism. -/
instance (a b : ℤ) : (torAmplitudeIn C a b).IsClosedUnderIsomorphisms where
  of_iso e hM F := by
    obtain ⟨h₁, h₂⟩ := hM F
    exact ⟨TStructure.t.isGE_of_iso (whiskerRightIso e _) a,
      TStructure.t.isLE_of_iso (whiskerRightIso e _) b⟩

/-- Tor amplitude passes to retracts. -/
instance (a b : ℤ) : (torAmplitudeIn C a b).IsStableUnderRetracts where
  of_retract e h F := (homologyConcentratedIn a b).prop_of_retract
    (e.map (tensorRight ((singleFunctor C 0).obj F))) (h F)

variable (C)

/-- An object of `D(C)` has *finite Tor amplitude* if it has Tor amplitude in some interval
`[a, b]`. -/
def finiteTorAmplitude : ObjectProperty (DerivedCategory C) :=
  fun M ↦ ∃ a b : ℤ, torAmplitudeIn C a b M

/-- Finite Tor amplitude is invariant under isomorphism. -/
instance : (finiteTorAmplitude C).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨a, b, h⟩ ↦ ⟨a, b, (torAmplitudeIn C a b).prop_of_iso e h⟩

/-- Finite Tor amplitude passes to retracts. -/
instance : (finiteTorAmplitude C).IsStableUnderRetracts where
  of_retract e := fun ⟨a, b, h⟩ ↦ ⟨a, b, (torAmplitudeIn C a b).prop_of_retract e h⟩

variable {C}

/-- Let `P` be a property of objects of `D(C)` that are bounded for the canonical t-structure.
An object satisfies `P` and has finite Tor amplitude exactly when, for some interval `[a, b]`,
it satisfies `P`, has homology concentrated in `[a, b]` and has Tor amplitude in `[a, b]`. -/
lemma exists_inf_homologyConcentratedIn_inf_torAmplitudeIn_iff
    {P : ObjectProperty (DerivedCategory C)} (hP : P ≤ TStructure.t.bounded)
    (K : DerivedCategory C) :
    (∃ a b : ℤ, (P ⊓ homologyConcentratedIn a b ⊓ torAmplitudeIn C a b) K) ↔
      (P ⊓ finiteTorAmplitude C) K := by
  constructor
  · rintro ⟨a, b, ⟨hPK, -⟩, hta⟩
    exact ⟨hPK, a, b, hta⟩
  · rintro ⟨hPK, a, b, hta⟩
    obtain ⟨c, d, hcd⟩ := (exists_homologyConcentratedIn_iff_bounded K).2 (hP K hPK)
    exact ⟨min a c, max b d, ⟨hPK, hcd.mono (min_le_right _ _) (le_max_right _ _)⟩,
      hta.mono (min_le_left _ _) (le_max_left _ _)⟩

end DerivedCategory
