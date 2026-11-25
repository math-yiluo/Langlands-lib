import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-! # Finite freeness from local integral lattices and a finite mod-two quotient -/

noncomputable section

universe u v w

open Function Module Submodule

namespace Langlands.Algebra.IntegralLocalLattice

variable {M : Type u} [AddCommGroup M]
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

/-- Inclusion of the inverse image of a rational subspace induces a map modulo two. -/
def modTwoMap (f : M →ₗ[ℤ] V) (W : Submodule ℚ V) :
    ModN ((W.restrictScalars ℤ).comap f) 2 →ₗ[ℤ] ModN M 2 :=
  (LinearMap.range (LinearMap.lsmul ℤ ((W.restrictScalars ℤ).comap f) 2)).mapQ
    (LinearMap.range (LinearMap.lsmul ℤ M 2))
    ((W.restrictScalars ℤ).comap f).subtype (by
      rintro _ ⟨x, rfl⟩
      exact ⟨(x : M), rfl⟩)

/-- Rational subspaces are closed under division by two, so this induced map is injective. -/
theorem modTwoMap_injective (f : M →ₗ[ℤ] V) (W : Submodule ℚ V) :
    Injective (modTwoMap f W) := by
  apply (modTwoMap f W).ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro q hq
  obtain ⟨x, rfl⟩ :=
    (LinearMap.range (LinearMap.lsmul ℤ ((W.restrictScalars ℤ).comap f) 2)).mkQ_surjective q
  change modTwoMap f W _ = 0 at hq
  rw [modTwoMap, Submodule.mkQ_apply, Submodule.mapQ_apply,
    Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨y, hy⟩ := hq
  change (2 : ℤ) • y = (x : M) at hy
  have hyW : f y ∈ W := by
    apply (W.smul_mem_iff (by norm_num : (2 : ℚ) ≠ 0)).mp
    have hxW : f (x : M) ∈ W := x.property
    rw [← hy] at hxW
    simpa only [ofNat_smul_eq_nsmul, map_nsmul] using hxW
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨⟨y, hyW⟩, Subtype.ext hy⟩

/-- A finite independent family is bounded in size by the mod-two quotient. -/
theorem independent_card_le_modTwo_card (f : M →ₗ[ℤ] V) (hf : Injective f)
    [Finite (ModN M 2)]
    (hlocal : ∀ W : Submodule ℚ V, W.FG → ((W.restrictScalars ℤ).comap f).FG)
    {ι : Type w} [Fintype ι] (a : ι → M) (ha : LinearIndependent ℚ (f ∘ a)) :
    Fintype.card ι ≤ Nat.card (ModN M 2) := by
  let W : Submodule ℚ V := span ℚ (Set.range (f ∘ a))
  let N : Submodule ℤ M := (W.restrictScalars ℤ).comap f
  have hN : N.FG := hlocal W (fg_span (Set.finite_range _))
  have : Module.Finite ℤ N := Module.Finite.of_fg hN
  have : HasUniqueDiv V := .of_module_rat V
  have : Module.IsTorsionFree ℤ M := hf.moduleIsTorsionFree f (by simp)
  have : Module.Free ℤ N := inferInstance
  let b : ι → N := fun i => ⟨a i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hb : LinearIndependent ℤ b := by
    apply LinearIndependent.of_comp (f.comp N.subtype)
    exact ha.restrict_scalars' ℤ
  have hcard := hb.fintype_card_le_finrank
  have hpow : Module.finrank ℤ N ≤ 2 ^ Module.finrank ℤ N := by
    have h : ∀ n : ℕ, n ≤ 2 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n hn =>
        rw [pow_succ]
        have hp : 0 < 2 ^ n := pow_pos (by decide) _
        omega
    exact h _
  have hmod : Nat.card (ModN N 2) ≤ Nat.card (ModN M 2) :=
    Nat.card_le_card_of_injective (modTwoMap f W) (modTwoMap_injective f W)
  rw [ModN.natCard_eq] at hmod
  exact hcard.trans (hpow.trans hmod)

/-- The local integral lattice criterion with a finite mod-two quotient. -/
def FiniteFreeStatement : Prop :=
  ∀ (M : Type u) [AddCommGroup M]
    (V : Type v) [AddCommGroup V] [Module ℚ V]
    (f : M →ₗ[ℤ] V), Injective f → Finite (ModN M 2) →
    (∀ W : Submodule ℚ V, W.FG → ((W.restrictScalars ℤ).comap f).FG) →
    Module.Free ℤ M ∧ Module.Finite ℤ M

/-- Local finite generation and a finite mod-two quotient imply finite freeness. -/
theorem finiteFree : FiniteFreeStatement.{u, v} := by
  intro M _ V _ _ f hf hmod hlocal
  have : Finite (ModN M 2) := hmod
  obtain ⟨ι, a, _ha, hspan, hind⟩ := exists_linearIndependent' ℚ f
  have hcard : Cardinal.mk ι ≤ (Nat.card (ModN M 2) : Cardinal) := by
    apply Cardinal.card_le_of
    intro s
    have h := independent_card_le_modTwo_card f hf hlocal
      (a ∘ ((↑) : s → ι)) (hind.comp ((↑) : s → ι) Subtype.coe_injective)
    simpa using h
  have : Finite ι := Cardinal.lt_aleph0_iff_finite.mp
    (hcard.trans_lt Cardinal.natCast_lt_aleph0)
  have hW : (span ℚ (Set.range f)).FG := by
    rw [← hspan]
    exact fg_span (Set.finite_range _)
  have htop : ((span ℚ (Set.range f)).restrictScalars ℤ).comap f = ⊤ := by
    apply top_unique
    intro x _
    exact Submodule.subset_span ⟨x, rfl⟩
  have hfg := hlocal (span ℚ (Set.range f)) hW
  rw [htop] at hfg
  have : Module.Finite ℤ M := ⟨hfg⟩
  have : HasUniqueDiv V := .of_module_rat V
  have : Module.IsTorsionFree ℤ M := hf.moduleIsTorsionFree f (by simp)
  exact ⟨inferInstance, inferInstance⟩

end Langlands.Algebra.IntegralLocalLattice
