/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Algebra.Category.ModuleCat.TowerLimitInducedMaps
public import WeilConjectures.RingTheory.FiniteOverCompleteRing

/-!
# Finiteness of the limit of a tower of finite modules with Bockstein sequences

Let `Λ` be a noetherian `ϖ`-adically complete ring (e.g. `Λ = 𝒪_E`) and `(Mₙ)` a tower of finite
`Λ`-modules, with transitions `tₙ : Mₙ₊₁ ⟶ Mₙ`, `ϖⁿ⁺¹ Mₙ = 0`, and maps `ιₙ : Mₙ ⟶ Mₙ₊₁` with
`ιₙ ∘ tₙ = ϖ` and `tₙ ∘ ιₙ = ϖ`, such that `Mₙ --ιₙ--> Mₙ₊₁ ⟶ M₀` is exact. This is the situation
of the cohomology `Mₙ = Hⁱ(Fₙ)` of the reductions `Fₙ = L ⧸ ϖⁿ⁺¹` of a `ϖ`-torsion free object
`L`, with `ιₙ` induced by the multiplication `ϖ : Fₙ ⟶ Fₙ₊₁` (exact sequences
`0 ⟶ Fₙ ⟶ Fₙ₊₁ ⟶ F₀ ⟶ 0`); for instance the stalks of `Rⁱg_*` of the reductions of an
`𝒪_E`-lattice in a lisse `ℓ`-adic sheaf. Then `lim Mₙ` is a finite `Λ`-module
(`ModuleCat.finite_limit_of_exact_reduction`): the kernel of `lim Mₙ ⟶ M₀` is `ϖ lim Mₙ` by a
compactness (König) argument, so `lim Mₙ ⧸ ϖ` embeds in `M₀`, and `lim Mₙ` is `ϖ`-adically
separated; the complete Nakayama lemma (`Module.finite_and_span_eq_top_of_adicComplete`)
concludes.

Unlike `ModuleCat.finite_limit_of_exact_tateSubmodule`, no global object `L` with `Mₙ` described
in terms of the cohomology of `L` is needed.
-/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite

namespace ModuleCat

variable {Λ : Type u} [CommRing Λ] (ϖ : Λ) (M : ℕᵒᵖ ⥤ ModuleCat.{v} Λ)

/-- Under the hypotheses of `ModuleCat.finite_limit_of_exact_reduction`, an element of `lim Mₙ`
vanishing in `M₀` is divisible by `ϖ`. -/
lemma mem_smul_top_of_limit_π_zero_eq_zero [∀ n, Finite (M.obj (op n))]
    (ι : ∀ n : ℕ, M.obj (op n) →ₗ[Λ] M.obj (op (n + 1)))
    (hιt : ∀ (n : ℕ) (x : M.obj (op (n + 1))),
      ι n (M.map (homOfLE (Nat.le_add_right n 1)).op x) = ϖ • x)
    (htι : ∀ (n : ℕ) (x : M.obj (op n)),
      M.map (homOfLE (Nat.le_add_right n 1)).op (ι n x) = ϖ • x)
    (hexact : ∀ n : ℕ, Function.Exact (ι n) (M.map (homOfLE (Nat.zero_le (n + 1))).op))
    (hkill : ∀ (n : ℕ) (x : M.obj (op n)), ϖ ^ (n + 1) • x = 0)
    (x : ↑(limit M)) (hx : limit.π M (op 0) x = 0) :
    x ∈ (Ideal.span {ϖ} • ⊤ : Submodule Λ ↑(limit M)) := by
  classical
  let t (n : ℕ) := M.map (homOfLE (Nat.le_add_right n 1)).op
  let xs (n : ℕ) := limit.π M (op n) x
  have hxs (n : ℕ) : t n (xs (n + 1)) = xs n := limit.w_apply M _ x
  -- the nonempty finite sets of preimages `Sₙ = ι⁻¹(xₙ₊₁)`
  let S (n : ℕ) := {y : M.obj (op n) // ι n y = xs (n + 1)}
  have hS (n : ℕ) : Nonempty (S n) := by
    obtain ⟨y, hy⟩ := ((hexact n) (xs (n + 1))).1
      ((limit.w_apply M (homOfLE (Nat.zero_le (n + 1))).op x).trans hx)
    exact ⟨⟨y, hy⟩⟩
  let r (n : ℕ) : S (n + 1) → S n := fun y ↦ ⟨t n y.1, by
    rw [hιt]
    exact (htι (n + 1) y.1).symm.trans
      ((congrArg (fun z ↦ t (n + 1) z) y.2).trans (hxs (n + 1)))⟩
  let F : ℕᵒᵖ ⥤ Type v := Functor.ofOpSequence (X := S) fun n ↦ TypeCat.ofHom (r n)
  have : ∀ j, Finite (F.obj j) := fun j ↦ Subtype.finite
  have : ∀ j, Nonempty (F.obj j) := fun j ↦ hS j.unop
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system F
  have hs' (n : ℕ) : t n (s (op (n + 1))).1 = (s (op n)).1 := by
    have := hs (homOfLE (Nat.le_add_right n 1)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at this
    exact congrArg Subtype.val this
  let Y := CategoryTheory.towerLimitMk (fun n ↦ (s (op n)).1) hs'
  have hxY : x = ϖ • Y := by
    refine Concrete.limit_ext _ _ _ fun ⟨n⟩ ↦ ?_
    rw [map_smul, limit_π_towerLimitMk]
    cases n with
    | zero =>
      change xs 0 = _
      rw [show xs 0 = 0 from hx, ← pow_one ϖ, hkill]
    | succ n =>
      rw [← hιt, hs' n]
      exact (s (op n)).2.symm
  rw [hxY]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) Submodule.mem_top

/-- **Finiteness of the limit of a tower of reductions.** Let `Λ` be a noetherian `ϖ`-adically
complete ring and `(Mₙ)` a tower of finite `Λ`-modules with `ϖⁿ⁺¹ Mₙ = 0`, together with maps
`ιₙ : Mₙ ⟶ Mₙ₊₁` such that `ιₙ ∘ tₙ = ϖ`, `tₙ ∘ ιₙ = ϖ` (`tₙ` the transitions) and
`Mₙ --ιₙ--> Mₙ₊₁ ⟶ M₀` is exact. Then `lim Mₙ` is a finite `Λ`-module. -/
theorem finite_limit_of_exact_reduction [IsNoetherianRing Λ] [IsAdicComplete (Ideal.span {ϖ}) Λ]
    [∀ n, Finite (M.obj (op n))]
    (ι : ∀ n : ℕ, M.obj (op n) →ₗ[Λ] M.obj (op (n + 1)))
    (hιt : ∀ (n : ℕ) (x : M.obj (op (n + 1))),
      ι n (M.map (homOfLE (Nat.le_add_right n 1)).op x) = ϖ • x)
    (htι : ∀ (n : ℕ) (x : M.obj (op n)),
      M.map (homOfLE (Nat.le_add_right n 1)).op (ι n x) = ϖ • x)
    (hexact : ∀ n : ℕ, Function.Exact (ι n) (M.map (homOfLE (Nat.zero_le (n + 1))).op))
    (hkill : ∀ (n : ℕ) (x : M.obj (op n)), ϖ ^ (n + 1) • x = 0) :
    Module.Finite Λ ↑(limit M) := by
  set I := Ideal.span {ϖ}
  -- `Iⁿ⁺¹` kills `Mₙ`
  have hkill' (n : ℕ) : (I ^ (n + 1) • ⊤ : Submodule Λ (M.obj (op n))) = ⊥ := by
    refine eq_bot_iff.2 (Submodule.smul_le.2 fun a ha m _ ↦ ?_)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [Submodule.mem_bot, mul_comm, mul_smul, hkill, smul_zero]
  -- the kernel of the projection to `M₀` is `I • lim Mₙ`
  have hker : LinearMap.ker (limit.π M (op 0)).hom = (I • ⊤ : Submodule Λ ↑(limit M)) := by
    refine le_antisymm (fun x hx ↦ mem_smul_top_of_limit_π_zero_eq_zero ϖ M ι hιt htι hexact
      hkill x hx) ?_
    have := Submodule.smul_top_le_comap_smul_top I (limit.π M (op 0)).hom
    refine this.trans fun x hx ↦ ?_
    have h0 := hkill' 0
    rw [zero_add, pow_one] at h0
    rw [Submodule.mem_comap, h0] at hx
    exact hx
  -- `lim Mₙ` is `I`-adically separated
  have : IsHausdorff I ↑(limit M) := ⟨fun x hx ↦ Concrete.limit_ext _ _ _ fun ⟨n⟩ ↦ by
    have h := Submodule.smul_top_le_comap_smul_top (I ^ (n + 1)) (limit.π M (op n)).hom
      ((SModEq.zero).1 (hx (n + 1)))
    rw [Submodule.mem_comap, hkill' n] at h
    rw [(Submodule.mem_bot Λ).1 h, map_zero]⟩
  -- `lim Mₙ ⧸ I` embeds in the finite module `M₀`
  have : Module.Finite Λ (LinearMap.range (limit.π M (op 0)).hom) := Module.Finite.of_finite
  have : Module.Finite Λ (↑(limit M) ⧸ (I • ⊤ : Submodule Λ ↑(limit M))) := by
    rw [← hker]
    exact Module.Finite.equiv (LinearMap.quotKerEquivRange _).symm
  have : Module.Finite (Λ ⧸ I) (↑(limit M) ⧸ (I • ⊤ : Submodule Λ ↑(limit M))) :=
    Module.Finite.of_restrictScalars_finite Λ _ _
  exact (Module.finite_and_span_eq_top_of_adicComplete I ↑(limit M)).1

end ModuleCat
