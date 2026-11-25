/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Torsion at a submonoid, localization, and torsion quotients

Mathlib's `Submodule.torsion' R M S` is the submodule of elements of `M` killed by some
element of the monoid `S`. This file adds the missing bridge to localization and the
functoriality of the quotient `M ⧸ torsion' R M S`, and specializes them to the
`a`-power-torsion submodule `Γ_(a)(M) = torsion' R M (Submonoid.powers a)`, which describes
the strict transform of a module on an affine chart.

## Main definitions

- `Submodule.powTorsion R M a`: the `a`-power-torsion submodule of `M`;
- `Submodule.torsion'QuotientMap`: the map induced on torsion quotients by a linear map.

## Main results

- `Submodule.torsion'_eq_ker`: the `S`-torsion submodule is the kernel of the
  localization map at `S`;
- `Submodule.localized'_torsion'`: localization maps `S`-torsion onto the torsion of the
  localized module;
- `Submodule.torsion'_quotient_eq_bot`: the torsion quotient is torsion free;
- `Submodule.torsion'QuotientMap_injective`,
  `Submodule.torsion'QuotientMap_surjective` and `Submodule.torsion'QuotientMap_exact`: a
  short exact sequence induces a short exact sequence of torsion quotients, provided it
  stays exact modulo `s • ⊤`; `Submodule.comap_smul_top_le_of_isSMulRegular` (in
  `WeilConjectures.Mathlib.Algebra.Exact.Basic`) supplies that hypothesis when `S` acts
  regularly on the third term;
- `IsLocalization.Away.ker_lift_comp_algebraMap_eq_comap_powTorsion`: the kernel of a ring
  map `C → B` inverting `a`, factored through `C[1/a]`, is the `a`-saturation of its kernel,
  i.e. the inverse image of the `a`-power torsion of the quotient.
-/

@[expose] public section

open Pointwise

namespace Submodule

section Defs

variable {R : Type*} [CommSemiring R]
variable (R) (M : Type*) [AddCommMonoid M] [Module R M]

/-- The `a`-power-torsion submodule `Γ_(a)(M)` of an `R`-module `M`: the elements killed
by some power of `a`. It is the `S`-torsion submodule for `S` the monoid of powers of `a`,
so it is a submodule by construction.
(Blueprint: `def:nagata-power-torsion`, `lemma:nagata-power-torsion-submodule`.) -/
def powTorsion (a : R) : Submodule R M :=
  torsion' R M (Submonoid.powers a)

variable {R M} {a : R}

/-- Membership in the power-torsion submodule.
(Blueprint: `lemma:nagata-mem-power-torsion`.) -/
lemma mem_powTorsion_iff {m : M} : m ∈ powTorsion R M a ↔ ∃ n : ℕ, a ^ n • m = 0 := by
  rw [powTorsion, mem_torsion'_iff]
  constructor
  · rintro ⟨⟨s, n, rfl⟩, hs⟩
    exact ⟨n, hs⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨a ^ n, n, rfl⟩, hn⟩

section Localization

variable {N : Type*} [AddCommMonoid N] [Module R N]

/-- The `S`-torsion submodule is the kernel of the localization map at `S`, stated for an
arbitrary realization `f : M →ₗ[R] N` of the localization. -/
theorem torsion'_eq_ker (S : Submonoid R) (f : M →ₗ[R] N) [IsLocalizedModule S f] :
    torsion' R M S = LinearMap.ker f := by
  ext m
  rw [LinearMap.mem_ker, IsLocalizedModule.eq_zero_iff S, mem_torsion'_iff]

/-- The power-torsion submodule is the kernel of the localization map `M → M_a`.
(Blueprint: `lemma:nagata-power-torsion-kernel-localization`.) -/
theorem powTorsion_eq_ker_localization (f : M →ₗ[R] N)
    [IsLocalizedModule (Submonoid.powers a) f] :
    powTorsion R M a = LinearMap.ker f :=
  torsion'_eq_ker _ f

variable (S' : Type*) [CommSemiring S'] [Algebra R S'] (p : Submonoid R) [IsLocalization p S']
variable [Module S' N] [IsScalarTower R S' N]

/-- Localization of torsion: for a localization `f : M →ₗ[R] N` at `p` over `S' = R_p`,
the localization of the `S`-torsion of `M` is the torsion of `N` at the image of `S`. -/
theorem localized'_torsion' (S : Submonoid R) (f : M →ₗ[R] N) [IsLocalizedModule p f] :
    (torsion' R M S).localized' S' p f = torsion' S' N (S.map (algebraMap R S')) := by
  ext x
  rw [mem_localized', mem_torsion'_iff]
  constructor
  · rintro ⟨m, ⟨⟨c, hc⟩, hm⟩, s, rfl⟩
    refine ⟨⟨algebraMap R S' c, c, hc, rfl⟩, ?_⟩
    rw [Submonoid.smul_def, algebraMap_smul, ← IsLocalizedModule.mk'_smul,
      show c • m = 0 from hm, IsLocalizedModule.mk'_zero]
  · rintro ⟨⟨_, c, hc, rfl⟩, hx⟩
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f x
    simp only [Function.uncurry_apply_pair] at hx ⊢
    rw [Submonoid.smul_def, algebraMap_smul, ← IsLocalizedModule.mk'_smul,
      IsLocalizedModule.mk'_eq_zero'] at hx
    obtain ⟨t, ht⟩ := hx
    exact ⟨t • m, ⟨⟨c, hc⟩, by rw [Submonoid.smul_def, smul_comm, ht]⟩, t * s,
      IsLocalizedModule.mk'_cancel_left f m t s⟩

/-- Localization of power torsion, the case `S = Submonoid.powers a` of
`Submodule.localized'_torsion'`: the localization of `Γ_(a)(M)` is the power torsion of
the localized module at the image of `a`.
(Blueprint: `lemma:nagata-power-torsion-localization`.) -/
theorem localized'_powTorsion (f : M →ₗ[R] N) [IsLocalizedModule p f] :
    (powTorsion R M a).localized' S' p f = powTorsion S' N (algebraMap R S' a) := by
  rw [powTorsion, localized'_torsion', powTorsion, Submonoid.map_powers]

end Localization

end Defs

section Quotient

variable {R : Type*} [CommRing R]
variable (R) (M : Type*) [AddCommGroup M] [Module R M] (S : Submonoid R)

/-- The torsion quotient is torsion free: no nonzero class of `M ⧸ torsion' R M S` is
killed by an element of `S`. -/
theorem torsion'_quotient_eq_bot : torsion' R (M ⧸ torsion' R M S) S = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨s, hs⟩
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hs
  obtain ⟨t, ht⟩ := hs
  rw [mem_bot, Submodule.Quotient.mk_eq_zero]
  exact ⟨t * s, by rw [mul_smul, Submonoid.smul_def s, ht]⟩

variable {S} in
/-- Every element of `S` acts regularly on the torsion quotient. -/
theorem isSMulRegular_quotient_torsion' {s : R} (hs : s ∈ S) :
    IsSMulRegular (M ⧸ torsion' R M S) s := by
  intro x y hxy
  rw [← sub_eq_zero, ← smul_sub] at hxy
  have hmem : x - y ∈ torsion' R (M ⧸ torsion' R M S) S := ⟨⟨s, hs⟩, hxy⟩
  rw [torsion'_quotient_eq_bot, mem_bot, sub_eq_zero] at hmem
  exact hmem

variable (a : R)

/-- The power-torsion quotient has no exceptional torsion.
(Blueprint: `lemma:nagata-power-torsion-quotient-torsionfree`.) -/
theorem powTorsion_quotient_eq_bot : powTorsion R (M ⧸ powTorsion R M a) a = ⊥ :=
  torsion'_quotient_eq_bot R M _

/-- Multiplication by `a` is injective on the power-torsion quotient.
(Blueprint: `lemma:nagata-power-torsion-quotient-torsionfree`.) -/
theorem isSMulRegular_quotient_powTorsion :
    IsSMulRegular (M ⧸ powTorsion R M a) a :=
  isSMulRegular_quotient_torsion' R M (Submonoid.mem_powers a)

end Quotient

section Functoriality

variable {R : Type*} [CommRing R] (S : Submonoid R)
variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]

/-- A linear map sends torsion to torsion; this is the induced map on torsion quotients. -/
def torsion'QuotientMap (f : M₁ →ₗ[R] M₂) :
    M₁ ⧸ torsion' R M₁ S →ₗ[R] M₂ ⧸ torsion' R M₂ S :=
  Submodule.mapQ _ _ f <| by
    rintro x ⟨s, hs⟩
    exact ⟨s, by rw [Submonoid.smul_def, ← map_smul, ← Submonoid.smul_def, hs, map_zero]⟩

@[simp]
lemma torsion'QuotientMap_mk (f : M₁ →ₗ[R] M₂) (x : M₁) :
    torsion'QuotientMap S f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) :=
  Submodule.mapQ_apply _ _ _ _

/-- The torsion quotient of an injective map is injective. -/
theorem torsion'QuotientMap_injective {f : M₁ →ₗ[R] M₂} (hf : Function.Injective f) :
    Function.Injective (torsion'QuotientMap S f) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro x hx
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, torsion'QuotientMap_mk, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨s, hs⟩ := hx
  rw [mem_bot, Submodule.Quotient.mk_eq_zero]
  refine ⟨s, hf ?_⟩
  rw [Submonoid.smul_def, map_smul, ← Submonoid.smul_def, hs, map_zero]

/-- The torsion quotient of a surjective map is surjective. -/
theorem torsion'QuotientMap_surjective {g : M₂ →ₗ[R] M₃} (hg : Function.Surjective g) :
    Function.Surjective (torsion'QuotientMap S g) := by
  rintro x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := hg m
  exact ⟨Submodule.Quotient.mk y, torsion'QuotientMap_mk _ _ _⟩

variable {S}

/-- Torsion quotients preserve exactness of a sequence which stays exact modulo `s • ⊤`
for every `s ∈ S` (Stacks Project Tag 080W). Together with
`Submodule.torsion'QuotientMap_injective` and `Submodule.torsion'QuotientMap_surjective`
this transforms a short exact sequence into a short exact sequence. -/
theorem torsion'QuotientMap_exact {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}
    (hfg : Function.Exact f g)
    (H : ∀ s : S, Submodule.comap f ((s : R) • (⊤ : Submodule R M₂)) ≤
      (s : R) • (⊤ : Submodule R M₁)) :
    Function.Exact (torsion'QuotientMap S f) (torsion'QuotientMap S g) := by
  rintro x
  constructor
  · intro hx
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [torsion'QuotientMap_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨s, hs⟩ := hx
    rw [Submonoid.smul_def, ← map_smul] at hs
    obtain ⟨w, hw⟩ := (hfg ((s : R) • m)).mp hs
    -- `w` maps into `s • M₂`, hence is itself divisible by `s`
    have hwmem : w ∈ Submodule.comap f ((s : R) • (⊤ : Submodule R M₂)) := by
      rw [Submodule.mem_comap, hw, mem_smul_pointwise_iff_exists]
      exact ⟨m, mem_top, rfl⟩
    obtain ⟨z, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp (H s hwmem)
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    rw [torsion'QuotientMap_mk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨s, by rw [Submonoid.smul_def, smul_sub, ← map_smul, hw, sub_self]⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [torsion'QuotientMap_mk, torsion'QuotientMap_mk, Submodule.Quotient.mk_eq_zero]
    exact ⟨1, by rw [Submonoid.smul_def, OneMemClass.coe_one, one_smul,
      hfg.apply_apply_eq_zero]⟩

end Functoriality

end Submodule

namespace IsLocalization.Away

open Submodule

variable {C B S : Type*} [CommRing C] [CommRing B] [CommRing S] [Algebra C S] {a : C}
  [IsLocalization.Away a S]

/-- **Affine scheme-image saturation** (blueprint:
`lemma:nagata-scheme-image-affine-saturation`). Let `f : C → B` be a ring map with kernel
`K` (so that `C ⧸ K → B` is injective), and let `a : C` map to a unit of `B`. Then the
kernel of the factorization `C → C[1/a] → B` is the `a`-saturation
`{c | ∃ n, a ^ n * c ∈ K}` of `K`, and it is the inverse image of the `a`-power torsion
`Γ_(a)(C ⧸ K)` under `C → C ⧸ K`.

On a blow-up chart this says that the scheme-theoretic image is the quotient by the
`a`-power torsion, i.e. the strict-transform chart; the global form of that consequence is
`AlgebraicGeometry.Scheme.Hom.ker_lift_admissibleBlowup`. -/
theorem ker_lift_comp_algebraMap_eq_comap_powTorsion (f : C →+* B) (ha : IsUnit (f a)) :
    (RingHom.ker ((lift a ha : S →+* B).comp (algebraMap C S)) : Set C) =
        {c | ∃ n : ℕ, a ^ n * c ∈ RingHom.ker f} ∧
      RingHom.ker ((lift a ha : S →+* B).comp (algebraMap C S)) =
        (powTorsion C (C ⧸ RingHom.ker f) a).comap (RingHom.ker f).mkQ := by
  rw [lift_comp]
  have key (c : C) : c ∈ RingHom.ker f ↔ ∃ n : ℕ, a ^ n * c ∈ RingHom.ker f := by
    refine ⟨fun hc ↦ ⟨0, by simpa using hc⟩, fun ⟨n, hn⟩ ↦ ?_⟩
    rw [RingHom.mem_ker, map_mul, map_pow] at hn
    exact (ha.pow n).mul_right_eq_zero.mp hn
  refine ⟨Set.ext key, ?_⟩
  ext c
  rw [key, mem_comap, mkQ_apply, mem_powTorsion_iff]
  simp_rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]

end IsLocalization.Away
