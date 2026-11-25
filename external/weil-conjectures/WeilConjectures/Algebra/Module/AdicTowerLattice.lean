/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Module.AdicTowerLimit
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Lattices in limits of `ℓ`-adic towers

Let `Λ` be a discrete valuation ring, `ℓ` a nonzero nonunit of `Λ` and `L` a finitely generated
`Λ`-module whose `ℓ`-power torsion is killed by `ℓᶜ`. Then `ℓᶜ L` is a free `Λ`-module of finite
rank `r` (`Module.isTorsionFree_range_nsmul`), and for every `m` and every map `e : L ⟶ M` with
kernel `ℓᵐ⁺ᶜ L`, the image `e(ℓᶜ L) ≅ ℓᶜL / ℓᵐ⁺ᶜL ≅ ℓᶜL / ℓᵐ(ℓᶜL)` is isomorphic to
`(Λ / ℓᵐ)ʳ` (`Module.exists_linearEquiv_range_comp_nsmul`).

This applies to the limit `L` of a tower `(Mₙ)` with `ℓ`-adic long exact sequences
(`ModuleCat.AdicTowerSequence`): the `ℓ`-power torsion of `lim M'ₙ` is killed by `ℓᶜ` as soon as
the tower `(Mₙ)` satisfies the Artin-Rees condition with constant `c`
(`ModuleCat.AdicTowerSequence.pow_smul_eq_zero_of_exists_eval_eq`).
-/

@[expose] public section

universe u v w

namespace IsDiscreteValuationRing

/-- In a discrete valuation ring, every nonzero element divides a power of any nonzero nonunit. -/
lemma exists_dvd_pow {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {a b : R}
    (ha : a ≠ 0) (hb : b ≠ 0) (hb' : ¬IsUnit b) : ∃ k : ℕ, a ∣ b ^ k := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨j, v, rfl⟩ := eq_unit_mul_pow_irreducible hb hϖ
  have hj : j ≠ 0 := by
    rintro rfl
    exact hb' (by simp)
  refine ⟨n, ?_⟩
  rw [mul_pow, ← pow_mul]
  exact (Units.mul_left_dvd.2 (pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n
    (Nat.pos_of_ne_zero hj)))).trans (dvd_mul_left _ _)

end IsDiscreteValuationRing

namespace Module

variable {Λ : Type u} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] {L : Type v}
  [AddCommGroup L] [Module Λ L]

/-- If `ℓ` is a nonzero nonunit of a discrete valuation ring `Λ` and the `ℓ`-power torsion of the
`Λ`-module `L` is killed by `ℓᶜ`, then `ℓᶜ L` is torsion free. -/
lemma isTorsionFree_range_nsmul {ℓ : ℕ} (hℓ : (ℓ : Λ) ≠ 0) (hℓ' : ¬IsUnit (ℓ : Λ)) {c : ℕ}
    (hc : ∀ (y : L) (k : ℕ), ℓ ^ k • y = 0 → ℓ ^ c • y = 0) :
    IsTorsionFree Λ (LinearMap.range (ℓ ^ c • LinearMap.id : L →ₗ[Λ] L)) := by
  refine .of_smul_eq_zero fun a p hap ↦ or_iff_not_imp_left.2 fun ha ↦ ?_
  obtain ⟨_, y, rfl⟩ := p
  obtain ⟨k, d, hd⟩ := IsDiscreteValuationRing.exists_dvd_pow ha hℓ hℓ'
  have h : ((ℓ ^ k : ℕ) : Λ) • (ℓ ^ c • y) = 0 := by
    rw [Nat.cast_pow, hd, mul_comm, mul_smul]
    exact (congrArg (d • ·) (congrArg Subtype.val hap)).trans (smul_zero d)
  rw [Nat.cast_smul_eq_nsmul, smul_smul, ← pow_add] at h
  exact Subtype.ext (hc y _ h)

/-- **Lattices in `ℓ`-adic limits.** Let `ℓ` be a nonzero nonunit of a discrete valuation ring
`Λ` and `L` a finitely generated `Λ`-module whose `ℓ`-power torsion is killed by `ℓᶜ`. Then
there is `r` (the rank of the free module `ℓᶜ L`) such that for every `m` and every linear map
`e : L ⟶ M` with kernel `ℓᵐ⁺ᶜ L`, the image `e(ℓᶜ L)` is isomorphic to `(Λ / ℓᵐ)ʳ`. -/
theorem exists_linearEquiv_range_comp_nsmul [Module.Finite Λ L] {ℓ : ℕ} (hℓ : (ℓ : Λ) ≠ 0)
    (hℓ' : ¬IsUnit (ℓ : Λ)) {c : ℕ} (hc : ∀ (y : L) (k : ℕ), ℓ ^ k • y = 0 → ℓ ^ c • y = 0) :
    ∃ r : ℕ, ∀ (m : ℕ) {M : Type w} [AddCommGroup M] [Module Λ M] (e : L →ₗ[Λ] M),
      (∀ x, e x = 0 ↔ ∃ y, ℓ ^ (m + c) • y = x) →
      Nonempty (LinearMap.range (e ∘ₗ (ℓ ^ c • LinearMap.id)) ≃ₗ[Λ]
        (Fin r → Λ ⧸ Ideal.span {(ℓ : Λ) ^ m})) := by
  set P := LinearMap.range (ℓ ^ c • LinearMap.id : L →ₗ[Λ] L)
  have := isTorsionFree_range_nsmul hℓ hℓ' hc
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := Λ) (M := P)
  refine ⟨r, fun m M _ _ e he ↦ ?_⟩
  set I : Ideal Λ := Ideal.span {(ℓ : Λ) ^ m}
  let φ : P →ₗ[Λ] (Fin r → Λ ⧸ I) := LinearMap.pi fun i ↦ I.mkQ ∘ₗ b.coord i
  have hφx (x : P) (i : Fin r) : φ x i = Submodule.Quotient.mk (b.repr x i) := rfl
  have hφ : Function.Surjective φ := fun f ↦ by
    choose g hg using fun i ↦ Submodule.Quotient.mk_surjective I (f i)
    refine ⟨b.equivFun.symm g, funext fun i ↦ ?_⟩
    rw [hφx, ← b.equivFun_apply, LinearEquiv.apply_symm_apply, hg]
  let g : P →ₗ[Λ] M := e ∘ₗ P.subtype
  have hker : LinearMap.ker g = LinearMap.ker φ := by
    ext x
    simp only [LinearMap.mem_ker, g, LinearMap.comp_apply, Submodule.subtype_apply, he]
    constructor
    · rintro ⟨y, hy⟩
      have hx : x = ((ℓ : Λ) ^ m) • (⟨ℓ ^ c • y, y, rfl⟩ : P) := by
        refine Subtype.ext ?_
        rw [Submodule.coe_smul, ← hy, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, smul_smul,
          ← pow_add]
      funext i
      rw [Pi.zero_apply, hφx, Submodule.Quotient.mk_eq_zero, hx, map_smul, Finsupp.smul_apply,
        smul_eq_mul, Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
    · intro hx
      have hd (i : Fin r) : (ℓ : Λ) ^ m ∣ b.repr x i := by
        have := congrFun hx i
        rwa [Pi.zero_apply, hφx, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at this
      choose d hd using hd
      obtain ⟨y, hy⟩ := (b.equivFun.symm d).2
      refine ⟨y, ?_⟩
      have hx' : x = ((ℓ : Λ) ^ m) • b.equivFun.symm d := by
        refine b.equivFun.injective (funext fun i ↦ ?_)
        rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, Basis.equivFun_apply, hd,
          Pi.smul_apply, smul_eq_mul]
      rw [hx', Submodule.coe_smul, ← hy, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul,
        LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← pow_add]
  have hrange : LinearMap.range (e ∘ₗ (ℓ ^ c • LinearMap.id)) = LinearMap.range g := by
    rw [LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
  exact ⟨LinearEquiv.ofEq _ _ hrange ≪≫ₗ (LinearMap.quotKerEquivRange g).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hker ≪≫ₗ LinearMap.quotKerEquivOfSurjective φ hφ⟩

end Module

namespace ModuleCat.AdicTowerSequence

variable {R : Type u} [CommRing R] {ℓ : ℕ} {M M' : CategoryTheory.Functor ℕᵒᵖ (ModuleCat.{v} R)}

open Opposite

/-- **Artin-Rees for `Mₙ` bounds the torsion of `lim M'ₙ`.** If the image of `Mₘ₊꜀ ⟶ Mₘ` is
contained in the image of `lim Mₙ` for every `m`, then the `ℓ`-power torsion of `lim M'ₙ` is
killed by `ℓᶜ`: an element of `lim M'ₙ` killed by `ℓᵏ` is `δₖ₊꜀ z`, and
`ℓᶜ δₖ₊꜀ z = δₖ (z mod ℓᵏ)` vanishes, `z mod ℓᵏ` coming from `lim Mₙ`. -/
theorem pow_smul_eq_zero_of_exists_eval_eq (S : AdicTowerSequence ℓ M M')
    [∀ n, Finite (M.obj n)] (c : ℕ)
    (hc : ∀ (m : ℕ) (z : M.obj (op (m + c))),
      ∃ x : sectionsSubmodule M, x.1 (op m) = towerMap M (Nat.le_add_right m c) z)
    (y : sectionsSubmodule M') (k : ℕ) (hk : ℓ ^ k • y = 0) : ℓ ^ c • y = 0 := by
  have hk' : ℓ ^ (k + c) • y = 0 := by
    rw [pow_add, mul_comm, mul_smul, hk, smul_zero]
  obtain ⟨z, rfl⟩ := (S.exists_limδ_eq_iff (k + c) y).2 hk'
  rw [← S.limδ_towerMap, ← S.exists_eval_eq_iff]
  exact hc k z

end ModuleCat.AdicTowerSequence
