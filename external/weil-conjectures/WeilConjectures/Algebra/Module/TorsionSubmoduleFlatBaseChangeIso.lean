/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Finiteness.Ideal
import WeilConjectures.AlgebraicGeometry.TorsionModuleFlatBaseChangeIso

/-!
# Flat base change of an ideal-power torsion submodule

Source: More on Algebra, Lemma 05EC, part (1)
(blueprint: lem-weil-pbc-torsion-submodule-flat-base-change-iso).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

/-- Finite generators and flat exactness lift bounded torsion into the tensor of T. -/
private theorem killed_by_fg_lift
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (I : Ideal R) (n : ℕ) (hfg : (I ^ n).FG)
    (M : Type w) [AddCommGroup M] [Module R M]
    (y : S ⊗[R] M) (hy : ∀ a : R, a ∈ I ^ n → a • y = 0) :
    ∃ z : S ⊗[R] Ideal.primaryComponent M I,
      (Ideal.primaryComponent M I).subtype.lTensor S z = y := by
  classical
  obtain ⟨s, hs⟩ := hfg
  let δ : M →ₗ[R] (s → M) := LinearMap.pi fun a ↦ (a : R) • LinearMap.id
  have hδ : ∀ z : S ⊗[R] M,
      TensorProduct.piRight R R S (fun _ : s ↦ M) (δ.lTensor S z) =
        fun a : s ↦ (a : R) • z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b m =>
      simp [δ, TensorProduct.tmul_smul]
    | add z z' hz hz' =>
      simp only [map_add, hz, hz']
      ext a
      exact (smul_add _ _ _).symm
  have hzero : δ.lTensor S y = 0 := by
    apply (TensorProduct.piRight R R S (fun _ : s ↦ M)).injective
    rw [hδ, map_zero]
    ext a
    exact hy a (hs ▸ Ideal.subset_span a.property)
  have hex := Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map δ)
  obtain ⟨z, hz⟩ := (hex y).mp hzero
  have hker : LinearMap.ker δ ≤ Ideal.primaryComponent M I := by
    intro m hm
    apply (Ideal.primaryComponent_mem M I m).mpr
    refine ⟨n, ?_⟩
    rw [← hs, ← Submodule.torsionBySet_eq_torsionBySet_span]
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    exact congrFun (LinearMap.mem_ker.mp hm) ⟨a, a.property⟩
  let j : LinearMap.ker δ →ₗ[R] Ideal.primaryComponent M I :=
    Submodule.inclusion hker
  refine ⟨j.lTensor S z, ?_⟩
  change ((Ideal.primaryComponent M I).subtype.lTensor S ∘ₗ j.lTensor S) z = y
  rw [← LinearMap.lTensor_comp]
  exact hz

/-- For a flat ring map inducing an isomorphism modulo a finitely generated ideal,
base change identifies the ideal-power torsion submodule.

Source: More on Algebra, Lemma 05EC, part (1)
(blueprint: lem-weil-pbc-torsion-submodule-flat-base-change-iso).
Proof:
Put `T = primaryComponent M I`. Every element of T is killed by a positive power
of I, so the torsion-module comparison of Lemma 05E9 gives a bijection
`T → S ⊗[R] T`. Flatness makes the tensor of `T.subtype` injective. Their composite
is the indicated map, proving injectivity.
For surjectivity, take an element y killed by `I ^ n`. Choose a finite generating
set s of `I ^ n`, using finite generation of I. Define the linear map
`δ : M → (s → M)` by `δ(m)(a) = a • m`. Tensoring δ and then applying the
finite-product tensor equivalence gives `z ↦ (a • z)`; this identity follows by
tensor induction. Thus y is in the kernel of the tensored δ. Flat exactness lifts
y to `S ⊗[R] ker δ`. Each element of `ker δ` is killed by the generators, hence
by all of `I ^ n`, so `ker δ ≤ T`. Map the lift into `S ⊗[R] T` and use the
surjectivity of the torsion-module comparison to write it as `1 ⊗ x`.
This is the finite test-map and flatness argument of 05EC (1), applied directly
to the generators of `I ^ n` rather than to the quotient by T. It also covers
exponent zero and the empty generating set without separate assumptions. -/
theorem Ideal.primaryComponent_baseChange_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (I : Ideal R) (hI : I.FG)
    (hflat : RingHom.Flat (algebraMap R S))
    (hquot : Function.Bijective
      (Ideal.quotientMap (Ideal.map (algebraMap R S) I)
        (algebraMap R S) Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M] :
    Function.Bijective
      ((Ideal.primaryComponent.map I (TensorProduct.mk R S M 1)) :
        Ideal.primaryComponent M I →ₗ[R]
          Ideal.primaryComponent (S ⊗[R] M) I) := by
  classical
  have : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  let T := Ideal.primaryComponent M I
  let q := Ideal.quotientMap (Ideal.map (algebraMap R S) I)
    (algebraMap R S) Ideal.le_comap_map
  have hiso : ∃ e : (R ⧸ I) ≃+* (S ⧸ I.map (algebraMap R S)),
      ∀ r : R, e (Ideal.Quotient.mk I r) =
        Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S r) := by
    refine ⟨RingEquiv.ofBijective q hquot, ?_⟩
    intro r
    change q (Ideal.Quotient.mk I r) = _
    exact Ideal.quotientMap_mk
  have htors : ∀ x : T, ∃ n : ℕ, 0 < n ∧
      ∀ a : R, a ∈ I ^ n → a • x = 0 := by
    intro x
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I (x : M)).mp x.property
    refine ⟨n + 1, Nat.succ_pos _, fun a ha ↦ Subtype.ext ?_⟩
    exact (Submodule.mem_torsionBySet_iff _ _).mp hn
      ⟨a, Ideal.pow_le_pow_right (Nat.le_succ n) ha⟩
  have hright := RingTheory.torsionModule_flat_baseChange_bijective
    (T := T) (algebraMap R S) hflat I hiso htors
  have hmodule : Module.compHom S (algebraMap R S) = (inferInstance : Module R S) := by
    ext r s
    exact (Algebra.smul_def r s).symm
  rw [hmodule] at hright
  have hT : Function.Bijective (TensorProduct.mk R S T 1) := by
    convert (TensorProduct.comm R T S).bijective.comp hright using 1
    ext x
    simp
  have hincl : Function.Injective (T.subtype.lTensor S) :=
    Module.Flat.lTensor_preserves_injective_linearMap T.subtype T.injective_subtype
  constructor
  · intro x x' hxx'
    apply hT.1
    apply hincl
    change (1 : S) ⊗ₜ[R] (x : M) = (1 : S) ⊗ₜ[R] (x' : M)
    exact congrArg Subtype.val hxx'
  · intro y
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem (S ⊗[R] M) I (y : S ⊗[R] M)).mp
      y.property
    obtain ⟨z, hz⟩ := killed_by_fg_lift I n hI.pow M (y : S ⊗[R] M)
      (fun a ha ↦ (Submodule.mem_torsionBySet_iff _ _).mp hn ⟨a, ha⟩)
    obtain ⟨x, hx⟩ := hT.2 z
    refine ⟨x, Subtype.ext ?_⟩
    change (1 : S) ⊗ₜ[R] (x : M) = (y : S ⊗[R] M)
    rw [← hz, ← hx]
    rfl
