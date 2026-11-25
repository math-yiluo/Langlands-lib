/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.TowerLimitInducedMaps
public import WeilConjectures.RingTheory.TateSubmoduleFinite

/-!
# Finiteness of the limit of the cohomology of the reductions of a complex

Let `Λ` be a noetherian ring, complete for the `ϖ`-adic topology (e.g. `Λ = 𝒪_E`), and `L` a
complex of `Λ`-modules. The cohomology modules `Mₙ = Hⁱ(L ⊗ᴸ Λ ⧸ ϖⁿ⁺¹)` of the reductions of `L`
form a tower, sitting in the Bockstein exact sequences

`0 ⟶ Hⁱ(L) ⧸ ϖⁿ⁺¹ ⟶ Mₙ ⟶ Hⁱ⁺¹(L)[ϖⁿ⁺¹] ⟶ 0`,

compatible with the transition maps (the quotient maps on the left, the multiplication by `ϖ`
on the right). This file proves that `lim Mₙ` is a finitely generated `Λ`-module as soon as
`Hⁱ(L) ⧸ ϖ` and `Hⁱ⁺¹(L)[ϖ]` are, for instance when `M₀ = Hⁱ(L ⊗ᴸ Λ ⧸ ϖ)` and `M₀' = Hⁱ⁺¹(...)`
are finite (`ModuleCat.finite_limit_of_exact_tateSubmodule`). Stalks of `Rⁱg_*(Λ ⧸ ϖⁿ⁺¹)` are of
this form, with `L` the stalk of `Rg_*(Λ)`.

Only the left half of the sequences is used: the map `Mₙ ⟶ Hⁱ⁺¹(L)` need not be surjective onto
the `ϖⁿ⁺¹`-torsion. The limit sits in an exact sequence `0 ⟶ Hⁱ(L)^ ⟶ lim Mₙ ⟶ T_ϖ Hⁱ⁺¹(L)`,
whose outer terms are finite by `Module.finite_adicCompletion` and
`Module.finite_tateSubmodule`.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits Opposite

namespace ModuleCat

variable {Λ : Type u} [CommRing Λ] (ϖ : Λ) (M : ℕᵒᵖ ⥤ ModuleCat.{v} Λ)
  {A B : Type w} [AddCommGroup A] [Module Λ A] [AddCommGroup B] [Module Λ B]
  (α : ∀ n : ℕ, A →ₗ[Λ] M.obj (op n)) (β : ∀ n : ℕ, M.obj (op n) →ₗ[Λ] B)

/-- The map `lim Mₙ ⟶ T_ϖ B` induced by maps `βₙ : Mₙ ⟶ B` intertwining the transitions with the
multiplication by `ϖ`, when `Mₙ` is killed by `ϖⁿ⁺¹`. -/
noncomputable def towerLimitToTateSubmodule
    (hβ : ∀ (n : ℕ) (x : M.obj (op (n + 1))),
      β n (M.map (homOfLE (Nat.le_add_right n 1)).op x) = ϖ • β (n + 1) x)
    (hkill : ∀ (n : ℕ) (x : M.obj (op n)), ϖ ^ (n + 1) • x = 0) :
    ↑(limit M) →ₗ[Λ] Module.tateSubmodule ϖ B :=
  LinearMap.codRestrict _ (LinearMap.pi fun n ↦ β n ∘ₗ (limit.π M (op n)).hom) fun x n ↦ by
    refine ⟨?_, ?_⟩
    · change ϖ ^ (n + 1) • β n (limit.π M (op n) x) = 0
      rw [← map_smul, hkill, map_zero]
    · change ϖ • β (n + 1) (limit.π M (op (n + 1)) x) = β n (limit.π M (op n) x)
      rw [← hβ, limit.w_apply]

variable {ϖ}

/-- The map `Â ⟶ lim Mₙ` induced by maps `αₙ : A ⟶ Mₙ` compatible with the transitions and
killing `ϖⁿ⁺¹ A`. -/
noncomputable def adicCompletionToTowerLimit
    (hα : ∀ (n : ℕ) (a : A), M.map (homOfLE (Nat.le_add_right n 1)).op (α (n + 1) a) = α n a)
    (hker : ∀ n : ℕ, (Ideal.span {ϖ} ^ (n + 1) • ⊤ : Submodule Λ A) ≤ LinearMap.ker (α n)) :
    AdicCompletion (Ideal.span {ϖ}) A →ₗ[Λ] ↑(limit M) where
  toFun x := towerLimitMk (fun n ↦ Submodule.liftQ _ (α n) (hker n) (x.val (n + 1))) fun n ↦ by
    obtain ⟨a, ha⟩ := Submodule.mkQ_surjective _ (x.val (n + 2))
    have h : x.val (n + 1) = Submodule.mkQ _ a := by
      rw [← x.property (Nat.le_succ (n + 1)), ← ha]
      rfl
    rw [← ha, h]
    exact hα n a
  map_add' x y := Concrete.limit_ext _ _ _ fun ⟨n⟩ ↦ by
    simp only [limit_π_towerLimitMk, map_add, AdicCompletion.val_add_apply]
  map_smul' c x := Concrete.limit_ext _ _ _ fun ⟨n⟩ ↦ by
    simp only [limit_π_towerLimitMk, map_smul, AdicCompletion.val_smul_apply, RingHom.id_apply]

lemma limit_π_adicCompletionToTowerLimit
    (hα : ∀ (n : ℕ) (a : A), M.map (homOfLE (Nat.le_add_right n 1)).op (α (n + 1) a) = α n a)
    (hker : ∀ n : ℕ, (Ideal.span {ϖ} ^ (n + 1) • ⊤ : Submodule Λ A) ≤ LinearMap.ker (α n))
    (n : ℕ) (x : AdicCompletion (Ideal.span {ϖ}) A) :
    limit.π M (op n) (adicCompletionToTowerLimit M α hα hker x) =
      Submodule.liftQ _ (α n) (hker n) (x.val (n + 1)) := by
  dsimp only [adicCompletionToTowerLimit, LinearMap.coe_mk, AddHom.coe_mk]
  exact limit_π_towerLimitMk _ _ n

/-- **Finiteness of the limit of a tower of Bockstein extensions.** Let `Λ` be a noetherian
`ϖ`-adically complete ring and `(Mₙ)` a tower of `Λ`-modules with `ϖⁿ⁺¹ Mₙ = 0`, together with
exact sequences `A ⧸ ϖⁿ⁺¹ ↪ Mₙ ⟶ B` (given by `αₙ : A ⟶ Mₙ` with kernel `ϖⁿ⁺¹ A` and
`βₙ : Mₙ ⟶ B`) compatible with the transitions, `βₙ` intertwining the transition of `M` with
the multiplication by `ϖ`. If `A ⧸ ϖ A` is finite and the `ϖ`-torsion `B[ϖ]` is finitely
generated, then `lim Mₙ` is a finite `Λ`-module.

This applies to `Mₙ = Hⁱ(L ⊗ᴸ Λ ⧸ ϖⁿ⁺¹)`, `A = Hⁱ(L)` and `B = Hⁱ⁺¹(L)` for a complex `L`. -/
theorem finite_limit_of_exact_tateSubmodule [IsNoetherianRing Λ]
    [IsAdicComplete (Ideal.span {ϖ}) Λ]
    (hα : ∀ (n : ℕ) (a : A), M.map (homOfLE (Nat.le_add_right n 1)).op (α (n + 1) a) = α n a)
    (hβ : ∀ (n : ℕ) (x : M.obj (op (n + 1))),
      β n (M.map (homOfLE (Nat.le_add_right n 1)).op x) = ϖ • β (n + 1) x)
    (hker : ∀ n : ℕ, LinearMap.ker (α n) = (Ideal.span {ϖ} ^ (n + 1) • ⊤ : Submodule Λ A))
    (hexact : ∀ n : ℕ, Function.Exact (α n) (β n))
    (hkill : ∀ (n : ℕ) (x : M.obj (op n)), ϖ ^ (n + 1) • x = 0)
    [Module.Finite Λ (A ⧸ (Ideal.span {ϖ} • ⊤ : Submodule Λ A))]
    (hB : (LinearMap.ker (ϖ • LinearMap.id : B →ₗ[Λ] B)).FG) :
    Module.Finite Λ ↑(limit M) := by
  let V := towerLimitToTateSubmodule ϖ M β hβ hkill
  let U := adicCompletionToTowerLimit M α hα fun n ↦ (hker n).ge
  have hπV (x : ↑(limit M)) (n : ℕ) :
      ((V x : Module.tateSubmodule ϖ B) : ℕ → B) n = β n (limit.π M (op n) x) := rfl
  have hUV : LinearMap.ker V = LinearMap.range U := by
    apply le_antisymm
    · intro x hx
      have hx' (n : ℕ) : β n (limit.π M (op n) x) = 0 := by
        rw [← hπV, LinearMap.mem_ker.1 hx]
        rfl
      choose a ha using fun n ↦ ((hexact n) _).1 (hx' n)
      have hsucc (n : ℕ) : α n (a (n + 1)) = limit.π M (op n) x := by
        rw [← hα, ha, limit.w_apply]
      have hc (n : ℕ) : a n ≡ a (n + 1) [SMOD (Ideal.span {ϖ} ^ n • ⊤ : Submodule Λ A)] := by
        rw [SModEq.sub_mem]
        have h : a n - a (n + 1) ∈ LinearMap.ker (α n) := by
          rw [LinearMap.mem_ker, map_sub, ha, hsucc, sub_self]
        rw [hker n] at h
        exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) h
      refine ⟨AdicCompletion.mk _ A (AdicCompletion.AdicCauchySequence.mk _ A a hc),
        Concrete.limit_ext _ _ _ fun ⟨n⟩ ↦ ?_⟩
      rw [limit_π_adicCompletionToTowerLimit]
      exact hsucc n
    · rintro _ ⟨y, rfl⟩
      refine LinearMap.mem_ker.2 (Subtype.ext (funext fun n ↦ ?_))
      obtain ⟨a, ha⟩ := Submodule.mkQ_surjective _ (y.val (n + 1))
      rw [hπV, limit_π_adicCompletionToTowerLimit, ← ha]
      exact (hexact n).apply_apply_eq_zero a
  have : Module.Finite Λ (Module.tateSubmodule ϖ B) := Module.finite_tateSubmodule hB
  have : Module.Finite Λ (AdicCompletion (Ideal.span {ϖ}) A) :=
    Module.finite_adicCompletion _ A (IsNoetherian.noetherian _)
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker V (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, hUV, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map U

end ModuleCat
