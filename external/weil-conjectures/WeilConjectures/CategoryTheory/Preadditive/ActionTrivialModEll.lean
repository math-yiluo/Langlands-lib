/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.Mathlib.NumberTheory.Basic

/-!

# Actions which are trivial modulo `ℓ` by `ℓ`-divisible elements

The `ℓ`-adic step of the finiteness of the action of the pro-`p` kernel `P'` on `ℚ̄_ℓ`-nearby
cycles (SGA 4½, [Th. finitude], §3.7). Let a group `G` act on an object `Y` of a preadditive
category by `ρ`, trivially modulo `ℓ`: `ρ τ ≫ π = π` for a map `π : Y ⟶ Z` such that every
endomorphism `f` of `Y` with `f ≫ π = 0` is divisible by `ℓ`. Then `ρ τ = 1 + ℓ g`, so
`ρ (τ ^ ℓ ^ m) - 1` is divisible by `ℓ ^ (m + 1)`
(`CategoryTheory.End.exists_map_pow_sub_one_eq_pow_smul`). Hence, if every element of `G` is an
`ℓ ^ m`-th power (e.g. `G` pro-`p`, `p ≠ ℓ`), `G` acts trivially in two cases:

* `Y` is killed by `ℓ ^ m`, e.g. nearby cycles with `𝒪_E / ℓ ^ m`-coefficients
  (`CategoryTheory.End.eq_one_of_comp_eq_of_forall_exists_pow`);
* no nonzero endomorphism of `Y` is divisible by every power of `ℓ`, e.g. nearby cycles with
  `𝒪_E`-coefficients, whose endomorphisms form a finitely generated `𝒪_E`-module
  (`CategoryTheory.End.eq_one_of_comp_eq_of_forall_exists_pow_of_separated`).

In a pretriangulated category, the reduction `π` modulo `ℓ` given by a distinguished triangle
`Y --ℓ--> Y --π--> Z ⟶ Y⟦1⟧` has the required property
(`CategoryTheory.Pretriangulated.exists_eq_nsmul_of_comp_eq_zero`), which gives
`CategoryTheory.End.eq_one_of_distinguished` and
`CategoryTheory.End.eq_one_of_distinguished_of_separated`.

-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- **Actions trivial modulo `ℓ` are trivial modulo `ℓ ^ (m + 1)` on `ℓ ^ m`-th powers**: let
`π : Y ⟶ Z` be such that every endomorphism `f` of `Y` with `f ≫ π = 0` is divisible by `ℓ`
(`f = ℓ • g`), and let a group act on `Y` by `ρ` compatibly with `π`:
```
      ρ τ
  Y ─────▶ Y
   ╲       │
  π ╲      │ π
     ╲     ▼
      ───▶ Z
```
Then `ρ τ = 1 + ℓ g`, and `ρ (τ ^ ℓ ^ m) - 1` is divisible by `ℓ ^ (m + 1)`. -/
theorem End.exists_map_pow_sub_one_eq_pow_smul {Y Z : C} (π : Y ⟶ Z) {ℓ : ℕ}
    (hπ : ∀ f : End Y, (f).asHom ≫ π = 0 → ∃ g : End Y, f = ℓ • g)
    {G : Type*} [Group G] (ρ : G →* End Y) (hρ : ∀ τ, (ρ τ).asHom ≫ π = π) (m : ℕ) (τ : G) :
    ∃ y : End Y, ρ (τ ^ ℓ ^ m) - 1 = (ℓ ^ (m + 1)) • y := by
  obtain ⟨g, hg⟩ := hπ (ρ τ - 1) (by
    rw [End.sub_asHom, Preadditive.sub_comp, hρ, End.one_asHom, Category.id_comp, sub_self])
  have hτ : ρ τ = 1 + ℓ * g := by rw [← nsmul_eq_mul, ← hg, add_sub_cancel]
  obtain ⟨y, hy⟩ := exists_one_add_natCast_mul_pow_sub_one_eq ℓ m g
  exact ⟨y, by rw [map_pow, hτ, hy, nsmul_eq_mul, Nat.cast_pow]⟩

/-- **Actions trivial modulo `ℓ` by `ℓ`-divisible groups are trivial**: let `Y` be killed by
`ℓ ^ m` and `π : Y ⟶ Z` such that every endomorphism `f` of `Y` with `f ≫ π = 0` is divisible by
`ℓ`. A group in which every element is an `ℓ ^ m`-th power, acting on `Y` by `ρ` with
`ρ τ ≫ π = π` for all `τ` (as in `End.exists_map_pow_sub_one_eq_pow_smul`), acts trivially. -/
theorem End.eq_one_of_comp_eq_of_forall_exists_pow {Y Z : C} (π : Y ⟶ Z) {ℓ m : ℕ}
    (hℓ : (ℓ ^ m) • 𝟙 Y = 0) (hπ : ∀ f : End Y, (f).asHom ≫ π = 0 → ∃ g : End Y, f = ℓ • g)
    {G : Type*} [Group G] (ρ : G →* End Y) (hρ : ∀ τ, (ρ τ).asHom ≫ π = π)
    (hdiv : ∀ σ : G, ∃ τ, τ ^ ℓ ^ m = σ) (σ : G) : ρ σ = 1 := by
  obtain ⟨τ, rfl⟩ := hdiv σ
  obtain ⟨y, hy⟩ := End.exists_map_pow_sub_one_eq_pow_smul π hπ ρ hρ m τ
  rw [← sub_eq_zero, hy]
  apply End.ext
  rw [End.nsmul_asHom, End.zero_asHom, pow_succ', mul_smul, ← Category.id_comp y.asHom,
    ← Preadditive.nsmul_comp, hℓ, zero_comp, smul_zero]

/-- **Actions trivial modulo `ℓ` on `ℓ`-adically separated objects are trivial**: let `Y` be an
object no nonzero endomorphism of which is divisible by every power of `ℓ`, and `π : Y ⟶ Z` such
that every endomorphism `f` of `Y` with `f ≫ π = 0` is divisible by `ℓ`. A group in which every
element is an `ℓ ^ m`-th power for every `m`, acting on `Y` by `ρ` with `ρ τ ≫ π = π` for all
`τ` (as in `End.exists_map_pow_sub_one_eq_pow_smul`), acts trivially. -/
theorem End.eq_one_of_comp_eq_of_forall_exists_pow_of_separated {Y Z : C} (π : Y ⟶ Z)
    {ℓ : ℕ} (hsep : ∀ f : End Y, (∀ m : ℕ, ∃ g : End Y, f = (ℓ ^ m) • g) → f = 0)
    (hπ : ∀ f : End Y, (f).asHom ≫ π = 0 → ∃ g : End Y, f = ℓ • g)
    {G : Type*} [Group G] (ρ : G →* End Y) (hρ : ∀ τ, (ρ τ).asHom ≫ π = π)
    (hdiv : ∀ (m : ℕ) (σ : G), ∃ τ, τ ^ ℓ ^ m = σ) (σ : G) : ρ σ = 1 := by
  rw [← sub_eq_zero]
  refine hsep _ fun m ↦ ?_
  obtain ⟨τ, rfl⟩ := hdiv m σ
  obtain ⟨y, hy⟩ := End.exists_map_pow_sub_one_eq_pow_smul π hπ ρ hρ m τ
  exact ⟨ℓ • y, by rw [hy, pow_succ, mul_smul]⟩

namespace Pretriangulated

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Endomorphisms vanishing modulo `ℓ` are divisible by `ℓ`**: for a distinguished triangle
```
      u = ℓ       π        δ
  Y ────────▶ Y ────▶ Z ────▶ Y⟦1⟧
```
every endomorphism `f` of `Y` with `f ≫ π = 0` factors through `u`, so it is `ℓ • g`. -/
theorem exists_eq_nsmul_of_comp_eq_zero {Y Z : C} {ℓ : ℕ} {u : Y ⟶ Y} (π : Y ⟶ Z)
    (δ : Z ⟶ Y⟦(1 : ℤ)⟧) (hT : Triangle.mk u π δ ∈ distTriang C) (hu : u = ℓ • 𝟙 Y)
    (f : End Y) (hf : (f).asHom ≫ π = 0) : ∃ g : End Y, f = ℓ • g := by
  obtain ⟨g, hg⟩ : ∃ g : Y ⟶ Y, f.asHom = g ≫ u := Triangle.coyoneda_exact₂ _ hT f.asHom hf
  refine ⟨End.of g, End.ext ?_⟩
  change f.asHom = ℓ • g
  rw [hg, hu, Preadditive.comp_nsmul, Category.comp_id]

end Pretriangulated

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Actions trivial modulo `ℓ` by `ℓ`-divisible groups are trivial**, for `Y` killed by `ℓ ^ m`
and the reduction `π : Y ⟶ Z` modulo `ℓ` given by a distinguished triangle
```
      u = ℓ       π        δ
  Y ────────▶ Y ────▶ Z ────▶ Y⟦1⟧
```
(`End.eq_one_of_comp_eq_of_forall_exists_pow`). -/
theorem End.eq_one_of_distinguished {Y Z : C} {ℓ m : ℕ} {u : Y ⟶ Y} (π : Y ⟶ Z)
    (δ : Z ⟶ Y⟦(1 : ℤ)⟧) (hT : Triangle.mk u π δ ∈ distTriang C) (hu : u = ℓ • 𝟙 Y)
    (hℓ : (ℓ ^ m) • 𝟙 Y = 0) {G : Type*} [Group G] (ρ : G →* End Y) (hρ : ∀ τ, (ρ τ).asHom ≫ π = π)
    (hdiv : ∀ σ : G, ∃ τ, τ ^ ℓ ^ m = σ) (σ : G) : ρ σ = 1 :=
  End.eq_one_of_comp_eq_of_forall_exists_pow π hℓ
    (Pretriangulated.exists_eq_nsmul_of_comp_eq_zero π δ hT hu) ρ hρ hdiv σ

/-- **Actions trivial modulo `ℓ` on `ℓ`-adically separated objects are trivial**, for the
reduction `π : Y ⟶ Z` modulo `ℓ` given by a distinguished triangle
```
      u = ℓ       π        δ
  Y ────────▶ Y ────▶ Z ────▶ Y⟦1⟧
```
(`End.eq_one_of_comp_eq_of_forall_exists_pow_of_separated`). -/
theorem End.eq_one_of_distinguished_of_separated {Y Z : C} {ℓ : ℕ} {u : Y ⟶ Y} (π : Y ⟶ Z)
    (δ : Z ⟶ Y⟦(1 : ℤ)⟧) (hT : Triangle.mk u π δ ∈ distTriang C) (hu : u = ℓ • 𝟙 Y)
    (hsep : ∀ f : End Y, (∀ m : ℕ, ∃ g : End Y, f = (ℓ ^ m) • g) → f = 0)
    {G : Type*} [Group G] (ρ : G →* End Y) (hρ : ∀ τ, (ρ τ).asHom ≫ π = π)
    (hdiv : ∀ (m : ℕ) (σ : G), ∃ τ, τ ^ ℓ ^ m = σ) (σ : G) : ρ σ = 1 :=
  End.eq_one_of_comp_eq_of_forall_exists_pow_of_separated π hsep
    (Pretriangulated.exists_eq_nsmul_of_comp_eq_zero π δ hT hu) ρ hρ hdiv σ

end CategoryTheory
