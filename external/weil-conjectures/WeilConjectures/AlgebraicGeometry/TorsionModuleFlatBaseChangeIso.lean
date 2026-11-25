/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Module.Torsion.Basic
import WeilConjectures.RingTheory.BijectiveQuotientMapPowOfFlat

@[expose] public section

set_option autoImplicit false

/-! # I-power torsion modules and flat base change

Source: Stacks Project, More on Algebra, Lemma 05E9 (implication (2) => (1))
(blueprint: lem-weil-pbc-torsion-module-flat-base-change-iso).
-/

open scoped TensorProduct

namespace RingTheory

/-- If `J` annihilates `M`, an isomorphism modulo `J` suffices for base change.
The inverse quotient equivalence and the tensor-quotient equivalence give a left inverse.
Every pure tensor lifts because its coefficient agrees modulo `JS` with an element of `R`;
ideal-span induction kills the difference, and tensor induction handles sums. -/
private theorem killedModule_baseChange_bijective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (J : Ideal R)
    (hquot : Function.Bijective (Ideal.quotientMap (J.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (hkill : ∀ r ∈ J, ∀ x : M, r • x = 0) :
    Function.Bijective (fun x : M ↦ x ⊗ₜ[R] (1 : S)) := by
  classical
  let e := AlgEquiv.ofBijective
    (Ideal.quotientMapₐ (J.map (algebraMap R S)) (Algebra.ofId R S)
      Ideal.le_comap_map) hquot
  let q : S →ₗ[R] R ⧸ J :=
    (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R (J.map (algebraMap R S)))).toLinearMap
  have hbot : (J • ⊤ : Submodule R M) = ⊥ := by
    apply bot_unique
    exact Submodule.smul_le.mpr fun r hr x _ ↦ by
      simpa only [Submodule.mem_bot] using hkill r hr x
  let d : M ⊗[R] S →ₗ[R] M :=
    (Submodule.quotEquivOfEqBot _ hbot).toLinearMap ∘ₗ
      (TensorProduct.tensorQuotEquivQuotSMul M J).toLinearMap ∘ₗ q.lTensor M
  have hd : ∀ x : M, d (x ⊗ₜ[R] (1 : S)) = x := by
    intro x
    have hq : q 1 = Ideal.Quotient.mk J 1 := by
      simp [q]
    change (Submodule.quotEquivOfEqBot _ hbot)
      ((TensorProduct.tensorQuotEquivQuotSMul M J) (x ⊗ₜ[R] q 1)) = x
    rw [hq, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
    simp
  refine ⟨Function.LeftInverse.injective hd, ?_⟩
  have hv : ∀ b ∈ J.map (algebraMap R S), ∀ x : M, ∀ s : S,
      x ⊗ₜ[R] (b * s) = 0 := by
    intro b hb
    change b ∈ Ideal.span ((algebraMap R S) '' (J : Set R)) at hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨r, hr, rfl⟩ := hb
      intro x s
      rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, hkill r hr x,
        TensorProduct.zero_tmul]
    | zero => intro x s; simp
    | add b c hb hc ihb ihc =>
      intro x s
      simp [add_mul, TensorProduct.tmul_add, ihb, ihc]
    | smul a b hb ih =>
      intro x s
      simpa only [smul_eq_mul, mul_assoc, mul_left_comm a b s] using ih x (a * s)
  have hgen : ∀ x : M, ∀ s : S, ∃ y : M, y ⊗ₜ[R] (1 : S) = x ⊗ₜ[R] s := by
    intro x s
    obtain ⟨a, ha⟩ := hquot.2 (Ideal.Quotient.mk _ s)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hr : s - algebraMap R S r ∈ J.map (algebraMap R S) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa using (congrArg (fun z ↦ Ideal.Quotient.mk _ s - z) ha)
    have hz := hv (s - algebraMap R S r) hr x 1
    simp only [mul_one, TensorProduct.tmul_sub] at hz
    refine ⟨r • x, ?_⟩
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    exact (sub_eq_zero.mp hz).symm
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x s => exact hgen x s
  | add z w hz hw =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    exact ⟨x + y, TensorProduct.add_tmul _ _ _⟩

/-- For a flat ring map inducing an isomorphism modulo an ideal, base change
preserves every module whose elements are killed by powers of that ideal.
The proof follows Lemma 05E9: the case killed by `I`, induction through
`I ^ n M`, and passage to the directed union of the bounded torsion parts.
- (blueprint: lem-weil-pbc-torsion-module-flat-base-change-iso)
- Proof source: Stacks Project, More on Algebra, Lemma 05E9, lines 24277--24298;
  it uses only flatness, tensor right exactness and colimit compatibility.
-/
theorem torsionModule_flat_baseChange_bijective
    {R S T : Type*} [CommRing R] [CommRing S] [AddCommGroup T] [Module R T]
    (φ : R →+* S) (hflat : RingHom.Flat φ) (I : Ideal R)
    (hiso : ∃ e : (R ⧸ I) ≃+* (S ⧸ I.map φ),
      ∀ r : R, e (Ideal.Quotient.mk I r) =
        Ideal.Quotient.mk (I.map φ) (φ r)) :
    (∀ x : T, ∃ n : ℕ, 0 < n ∧
      ∀ y : R, y ∈ I ^ n → y • x = 0) →
    Function.Bijective
      (fun x : T =>
        @TensorProduct.mk R _ T S _ _ _ (Module.compHom S φ) x 1) := by
  let := φ.toAlgebra
  let : Module.Flat R S := hflat
  intro ht
  obtain ⟨e, he⟩ := hiso
  have hquot : Function.Bijective
      (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map) := by
    have heq : Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map = e.toRingHom := by
      apply Ideal.Quotient.ringHom_ext
      ext r
      exact (he r).symm
    rw [heq]
    exact e.bijective
  have hp := RingHom.bijective_quotientMap_pow_of_flat φ hflat I hquot
  have hlocal : ∀ x : T, ∃ (N : Submodule R T), x ∈ N ∧
      Function.Bijective (fun y : N ↦ y ⊗ₜ[R] (1 : S)) := by
    intro x
    obtain ⟨n, hn, hx⟩ := ht x
    let N := Submodule.torsionBySet R T (I ^ n : Ideal R)
    have hxN : x ∈ N := by
      exact (Submodule.mem_torsionBySet_iff _ _).mpr fun r ↦ hx r r.property
    refine ⟨N, hxN, killedModule_baseChange_bijective (I ^ n) (hp n hn) ?_⟩
    intro r hr y
    apply Subtype.ext
    exact (Submodule.mem_torsionBySet_iff _ _).mp y.property ⟨r, hr⟩
  have hinj : Function.Injective (fun x : T ↦ x ⊗ₜ[R] (1 : S)) := by
    change Function.Injective ((TensorProduct.mk R T S).flip 1)
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro x hx
    obtain ⟨N, hxN, hN⟩ := hlocal x
    have hNi := Module.Flat.rTensor_preserves_injective_linearMap
      (M := S) N.subtype Subtype.val_injective
    have hz : (⟨x, hxN⟩ : N) ⊗ₜ[R] (1 : S) = 0 := by
      apply hNi
      simpa using hx
    have he : (⟨x, hxN⟩ : N) = 0 := hN.1 (by simpa using hz)
    exact congrArg Subtype.val he
  refine ⟨hinj, ?_⟩
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x s =>
    obtain ⟨N, hxN, hN⟩ := hlocal x
    obtain ⟨y, hy⟩ := hN.2 ((⟨x, hxN⟩ : N) ⊗ₜ[R] s)
    refine ⟨y.val, ?_⟩
    exact congrArg (N.subtype.rTensor S) hy
  | add z w hz hw =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    exact ⟨x + y, by simp⟩

end RingTheory
