/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Splitting a unit by a normalized trace

Let `u : G ⟶ T` be a morphism in a preadditive category (typically the unit `G ⟶ Rπ_* π^* G` of
a finite étale cover `π` of degree `d`) and `t : T ⟶ G` a *trace* with `u ≫ t = d • 𝟙 G`. If
multiplication by `d` on `G` is invertible (for instance `d` is a power of `p` and the
coefficients are `ℤ[1/p]`-linear, as for `ℚ̄_ℓ`, `E`, `𝒪_E` or a finite ring `Λ` with `p ∈ Λˣ`), the
normalized trace `d⁻¹ t` is a retraction of `u` (`CategoryTheory.normalizedTrace`).

This file proves the formal parts of the averaging argument of SGA 4½, [Th. finitude], §3 and of
Illusie, *Autour du théorème de monodromie locale*, §4 (blueprint `prose-E-10`,
`lemma-duality-invariants-pro-p--1`):

* `CategoryTheory.comp_normalizedTrace`: `u ≫ d⁻¹ t = 𝟙`.
* `CategoryTheory.nsmul_normalizedTrace_comp_eq_sum` (*Galois averaging*): if a finite group of
  endomorphisms `ρ i` of `T` fixes `u` and `t ≫ u = ∑ i, ρ i` (the norm factors through the
  invariants), then `u` is split by the normalized trace and `n • (d⁻¹ t ≫ u) = ∑ i, ρ i`, `n` the
  number of the `ρ i`: the idempotent of the splitting is the average of the action.
* `CategoryTheory.normalizedTrace_compat` (*tower compatibility*): normalized traces of a tower
  `G ⟶ T₀ ⟶ T₁ ⟶ ⋯` whose traces satisfy the transitivity `τ ≫ t₁ = e • t₀` (`d₁ = e d₀`) are
  compatible with the transition maps.
* `CategoryTheory.Limits.descNormalizedTrace` (*limit of the tower*): if the target of the limit
  unit is the colimit of the finite levels, compatible retractions of the finite levels glue to a
  retraction of the limit unit.
* `CategoryTheory.isSplitMono_map_of_isIso_map` (*stabilization*): if an additive functor `Φ`
  inverts the comparison `c : Tₙ ⟶ T` from a finite level, then `Φ.map u` is a split monomorphism
  for `u = uₙ ≫ c`.

For `ℓ`-adic coefficients the colimit hypothesis of the limit step fails in general: for the
constant sheaf `ℚ̄_ℓ` on a separably closed point and the pro-`p` torsor `P ⟶ pt`, the sections of
`π_* π^* ℚ̄_ℓ` are the *continuous* functions `P ⟶ ℚ̄_ℓ`, while the colimit of the finite levels are
the locally constant ones. The `ℓ`-adic averaging therefore goes through the stabilization lemma:
the action of a pro-`p` group on an `ℓ`-adic constructible object factors through a finite quotient
(a pro-`p` subgroup of `GL_r(𝒪_E)` meets an open pro-`ℓ` subgroup trivially, so it is finite).
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

section Normalized

variable {G T : C} (u : G ⟶ T) (t : T ⟶ G) (d : ℕ) [IsIso (d • 𝟙 G)]

/-- The *normalized trace* `d⁻¹ t : T ⟶ G`, for multiplication by `d` invertible on `G`. -/
noncomputable def normalizedTrace : T ⟶ G :=
  t ≫ inv (d • 𝟙 G)

variable {u t d}

/-- The normalized trace is a retraction of `u` when `u ≫ t = d • 𝟙 G`. -/
@[reassoc (attr := simp)]
lemma comp_normalizedTrace (h : u ≫ t = d • 𝟙 G) : u ≫ normalizedTrace t d = 𝟙 G := by
  rw [normalizedTrace, ← assoc, h, IsIso.hom_inv_id]

/-- A morphism admitting a trace `t` with `u ≫ t = d • 𝟙 G`, `d` invertible on `G`, is a split
monomorphism. -/
lemma isSplitMono_of_comp_eq_nsmul (h : u ≫ t = d • 𝟙 G) : IsSplitMono u :=
  IsSplitMono.mk' ⟨normalizedTrace t d, comp_normalizedTrace h⟩

variable (d) in
/-- Multiplication by `d` on the inverse of multiplication by `d` is the identity. -/
lemma nsmul_inv_nsmul_id : d • inv (d • 𝟙 G) = 𝟙 G := by
  have h := IsIso.inv_hom_id (d • 𝟙 G)
  rwa [Preadditive.comp_nsmul, comp_id] at h

/-- `d • normalizedTrace t d = t`. -/
lemma nsmul_normalizedTrace : d • normalizedTrace t d = t := by
  rw [normalizedTrace, ← Preadditive.comp_nsmul, nsmul_inv_nsmul_id, comp_id]

/-- **Galois averaging.** Let `ρ i` be finitely many endomorphisms of `T` fixing `u`
(`u ≫ ρ i = u`), indexed by a type with `d` elements, and let the trace `t` factor the norm
through `u`: `t ≫ u = ∑ i, ρ i`. If `u` is a monomorphism, then `u ≫ t = d • 𝟙`, so `u` is split by
the normalized trace, and `d • (d⁻¹ t ≫ u) = ∑ i, ρ i`: the idempotent of the splitting is the
average of the `ρ i`. -/
lemma comp_eq_nsmul_of_comp_eq_sum [Mono u] {ι : Type*} [Fintype ι] (ρ : ι → (T ⟶ T))
    (hρ : ∀ i, u ≫ ρ i = u) (ht : t ≫ u = ∑ i, ρ i) :
    u ≫ t = Fintype.card ι • 𝟙 G := by
  rw [← cancel_mono u, assoc, ht, Preadditive.comp_sum, Preadditive.nsmul_comp, id_comp]
  simp [hρ]

/-- **Galois averaging**, the idempotent: `d • (d⁻¹ t ≫ u) = ∑ i, ρ i` when `t ≫ u = ∑ i, ρ i`. -/
lemma nsmul_normalizedTrace_comp_eq_sum {ι : Type*} [Fintype ι] (ρ : ι → (T ⟶ T))
    (ht : t ≫ u = ∑ i, ρ i) :
    d • (normalizedTrace t d ≫ u) = ∑ i, ρ i := by
  rw [← Preadditive.nsmul_comp, nsmul_normalizedTrace, ht]

/-- **Galois averaging**, the splitting: if `u` is a monomorphism fixed by the `d` endomorphisms
`ρ i` and `t ≫ u = ∑ i, ρ i`, the normalized trace is a retraction of `u`. -/
lemma comp_normalizedTrace_of_comp_eq_sum [Mono u] {ι : Type*} [Fintype ι] (ρ : ι → (T ⟶ T))
    (hd : Fintype.card ι = d) (hρ : ∀ i, u ≫ ρ i = u) (ht : t ≫ u = ∑ i, ρ i) :
    u ≫ normalizedTrace t d = 𝟙 G :=
  comp_normalizedTrace (hd ▸ comp_eq_nsmul_of_comp_eq_sum ρ hρ ht)

end Normalized

/-- **Tower compatibility of normalized traces.** Let `u₀ : G ⟶ T₀`, `u₁ : G ⟶ T₁` with
traces of degrees `d₀`, `d₁ = e * d₀`, and a transition `τ : T₀ ⟶ T₁` with `τ ≫ t₁ = e • t₀`
(transitivity of traces in a tower of finite étale covers). Then the normalized traces are
compatible: `τ ≫ d₁⁻¹ t₁ = d₀⁻¹ t₀`. -/
lemma normalizedTrace_compat {G T₀ T₁ : C} (t₀ : T₀ ⟶ G) (t₁ : T₁ ⟶ G) (τ : T₀ ⟶ T₁)
    (d₀ e d₁ : ℕ) [IsIso (d₀ • 𝟙 G)] [IsIso (d₁ • 𝟙 G)] (hd : d₁ = e * d₀)
    (hτ : τ ≫ t₁ = e • t₀) :
    τ ≫ normalizedTrace t₁ d₁ = normalizedTrace t₀ d₀ := by
  rw [← cancel_mono (d₁ • 𝟙 G)]
  simp only [Preadditive.comp_nsmul, comp_id]
  rw [← Preadditive.comp_nsmul, nsmul_normalizedTrace, hτ]
  conv_rhs => rw [hd]
  rw [mul_smul, nsmul_normalizedTrace]

namespace Limits

omit [Preadditive C]

variable {J : Type*} [Category J] {G : C} {F : J ⥤ C} {c : Cocone F}

/-- **The limit of the tower.** If the target `c.pt` of the limit unit is the colimit of the finite
levels `F.obj j`, retractions `r j` of the units `u j : G ⟶ F.obj j` that are compatible with the
transition maps glue to a morphism `c.pt ⟶ G`. -/
noncomputable def descNormalizedTrace (hc : IsColimit c) (r : ∀ j, F.obj j ⟶ G)
    (hr : ∀ ⦃i j : J⦄ (f : i ⟶ j), F.map f ≫ r j = r i) : c.pt ⟶ G :=
  hc.desc ⟨G, { app j := r j, naturality i j f := by simp [hr f] }⟩

@[reassoc (attr := simp)]
lemma ι_descNormalizedTrace (hc : IsColimit c) (r : ∀ j, F.obj j ⟶ G)
    (hr : ∀ ⦃i j : J⦄ (f : i ⟶ j), F.map f ≫ r j = r i) (j : J) :
    c.ι.app j ≫ descNormalizedTrace hc r hr = r j :=
  hc.fac _ j

/-- The glued morphism of `CategoryTheory.Limits.descNormalizedTrace` is a retraction of the limit
unit `u = u j ≫ c.ι.app j` when the `r j` are retractions of the `u j`. -/
lemma comp_descNormalizedTrace (hc : IsColimit c) (r : ∀ j, F.obj j ⟶ G)
    (hr : ∀ ⦃i j : J⦄ (f : i ⟶ j), F.map f ≫ r j = r i) (u : G ⟶ c.pt) (j : J)
    (uj : G ⟶ F.obj j) (hu : uj ≫ c.ι.app j = u) (hj : uj ≫ r j = 𝟙 G) :
    u ≫ descNormalizedTrace hc r hr = 𝟙 G := by
  rw [← hu, assoc, ι_descNormalizedTrace, hj]

/-- **Pro-`p` trace splitting in the colimit case**: the limit unit is a split monomorphism. -/
lemma isSplitMono_of_isColimit (hc : IsColimit c) (r : ∀ j, F.obj j ⟶ G)
    (hr : ∀ ⦃i j : J⦄ (f : i ⟶ j), F.map f ≫ r j = r i) (u : G ⟶ c.pt) (j : J)
    (uj : G ⟶ F.obj j) (hu : uj ≫ c.ι.app j = u) (hj : uj ≫ r j = 𝟙 G) : IsSplitMono u :=
  IsSplitMono.mk' ⟨_, comp_descNormalizedTrace hc r hr u j uj hu hj⟩

end Limits

section Stabilization

omit [Preadditive C]

variable {D : Type*} [Category D] {G Tₙ T : C} (Φ : C ⥤ D)

/-- **Stabilization at a finite level.** Let the limit unit factor as `u = uₙ ≫ c` through a finite
level `Tₙ`, with a retraction `r` of `uₙ`. If a functor `Φ` inverts the comparison `c`, then
`Φ.map r` composed with `(Φ.map c)⁻¹` is a retraction of `Φ.map u`. -/
lemma map_comp_inv_map_comp_eq_id (uₙ : G ⟶ Tₙ) (c : Tₙ ⟶ T) (r : Tₙ ⟶ G) (hr : uₙ ≫ r = 𝟙 G)
    [IsIso (Φ.map c)] : Φ.map (uₙ ≫ c) ≫ inv (Φ.map c) ≫ Φ.map r = 𝟙 (Φ.obj G) := by
  rw [Φ.map_comp, assoc, IsIso.hom_inv_id_assoc, ← Φ.map_comp, hr, Φ.map_id]

/-- **Stabilization at a finite level**: `Φ.map (uₙ ≫ c)` is a split monomorphism when `Φ`
inverts `c` and `uₙ` has a retraction. -/
lemma isSplitMono_map_of_isIso_map (uₙ : G ⟶ Tₙ) (c : Tₙ ⟶ T) (r : Tₙ ⟶ G) (hr : uₙ ≫ r = 𝟙 G)
    [IsIso (Φ.map c)] : IsSplitMono (Φ.map (uₙ ≫ c)) :=
  IsSplitMono.mk' ⟨_, map_comp_inv_map_comp_eq_id Φ uₙ c r hr⟩

end Stabilization

end CategoryTheory
