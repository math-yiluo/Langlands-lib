/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Linear maps whose kernel and cokernel are killed by an ideal

Let `u : M →ₗ[A] N` be a linear map over a commutative ring whose kernel and cokernel
`N ⧸ range u` are annihilated by an ideal `I`. For `f, g ∈ I` we construct the linear map
`LinearMap.fgMap u hker hcoker hf hg : N →ₗ[A] M` ("`fg`"), `y ↦ g • x` for any `x` with
`u x = f • y`, which satisfies `fgMap ∘ u = (f * g) • id` and `u ∘ fgMap = (f * g) • id`.
We prove its naturality, a converse criterion, and deduce that the kernel and cokernel of the
reduction `M ⧸ J • ⊤ → N ⧸ J • ⊤` modulo any ideal `J` are killed by `I * I` (Stacks, Tag 0888).
The packaged statement for `I = K ^ t` is `LinearMap.ker_coker_annihilated_mod_ideal` in
`WeilConjectures.RingTheory.KernelCokernelAnnihilatedModIdeal`.
-/

@[expose] public section

namespace LinearMap

variable {A M N M' N' P R : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup M'] [Module A M'] [AddCommGroup N'] [Module A N']
  [AddCommGroup P] [Module A P] [AddCommGroup R] [Module A R]

/-- If the cokernel of `u` is killed by `I` and `f ∈ I`, then every `f • y` is in the range
of `u`. -/
theorem exists_apply_eq_smul_of_le_annihilator_coker {I : Ideal A} {u : M →ₗ[A] N}
    (hcoker : I ≤ Module.annihilator A (N ⧸ range u)) {f : A} (hf : f ∈ I) (y : N) :
    ∃ x, u x = f • y := by
  have h := Module.mem_annihilator.mp (hcoker hf) (Submodule.Quotient.mk y)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h

/-- If the kernel of `u` is killed by `I` and `g ∈ I`, then `g • x` only depends on `u x`. -/
theorem smul_eq_smul_of_le_annihilator_ker {I : Ideal A} {u : M →ₗ[A] N}
    (hker : I ≤ Module.annihilator A (ker u)) {g : A} (hg : g ∈ I) {x x' : M}
    (h : u x = u x') : g • x = g • x' := by
  have hmem : x - x' ∈ ker u := by simp [h]
  have h' := Module.mem_annihilator.mp (hker hg) ⟨x - x', hmem⟩
  rw [← sub_eq_zero, ← smul_sub]
  simpa [Subtype.ext_iff] using h'

/-- The map "`fg`" `N → M` attached to `u : M →ₗ[A] N` whose kernel and cokernel are killed by
an ideal `I`, and to `f g ∈ I`: it sends `y` to `g • x` for any `x` with `u x = f • y`. -/
noncomputable def fgMap (u : M →ₗ[A] N) {I : Ideal A}
    (hker : I ≤ Module.annihilator A (ker u))
    (hcoker : I ≤ Module.annihilator A (N ⧸ range u)) {f g : A} (hf : f ∈ I) (hg : g ∈ I) :
    N →ₗ[A] M where
  toFun y := g • (exists_apply_eq_smul_of_le_annihilator_coker hcoker hf y).choose
  map_add' y₁ y₂ := by
    rw [← smul_add]
    refine smul_eq_smul_of_le_annihilator_ker hker hg ?_
    rw [map_add, (exists_apply_eq_smul_of_le_annihilator_coker hcoker hf _).choose_spec,
      (exists_apply_eq_smul_of_le_annihilator_coker hcoker hf _).choose_spec,
      (exists_apply_eq_smul_of_le_annihilator_coker hcoker hf _).choose_spec, smul_add]
  map_smul' a y := by
    rw [RingHom.id_apply, smul_comm a g]
    refine smul_eq_smul_of_le_annihilator_ker hker hg ?_
    rw [map_smul, (exists_apply_eq_smul_of_le_annihilator_coker hcoker hf _).choose_spec,
      (exists_apply_eq_smul_of_le_annihilator_coker hcoker hf _).choose_spec, smul_comm]

variable {u : M →ₗ[A] N} {I : Ideal A} (hker : I ≤ Module.annihilator A (ker u))
  (hcoker : I ≤ Module.annihilator A (N ⧸ range u)) {f g : A} (hf : f ∈ I) (hg : g ∈ I)

/-- `fgMap u y = g • x` for every `x` with `u x = f • y`. -/
theorem fgMap_apply_of_apply_eq {y : N} {x : M} (hx : u x = f • y) :
    fgMap u hker hcoker hf hg y = g • x :=
  smul_eq_smul_of_le_annihilator_ker hker hg
    ((exists_apply_eq_smul_of_le_annihilator_coker hcoker hf y).choose_spec.trans hx.symm)

theorem fgMap_comp_self : fgMap u hker hcoker hf hg ∘ₗ u = (f * g) • LinearMap.id := by
  ext m
  rw [comp_apply, fgMap_apply_of_apply_eq hker hcoker hf hg (map_smul u f m), smul_apply,
    id_apply, smul_smul, mul_comm]

theorem comp_fgMap : u ∘ₗ fgMap u hker hcoker hf hg = (f * g) • LinearMap.id := by
  ext y
  rw [comp_apply, smul_apply, id_apply]
  obtain ⟨x, hx⟩ := exists_apply_eq_smul_of_le_annihilator_coker hcoker hf y
  rw [fgMap_apply_of_apply_eq hker hcoker hf hg hx, map_smul, hx, smul_smul, mul_comm]

/-- Naturality of `fgMap` with respect to commutative squares. -/
theorem comp_fgMap_eq_fgMap_comp {u' : M' →ₗ[A] N'}
    (hker' : I ≤ Module.annihilator A (ker u'))
    (hcoker' : I ≤ Module.annihilator A (N' ⧸ range u')) {a : M →ₗ[A] M'} {b : N →ₗ[A] N'}
    (hab : u' ∘ₗ a = b ∘ₗ u) :
    a ∘ₗ fgMap u hker hcoker hf hg = fgMap u' hker' hcoker' hf hg ∘ₗ b := by
  ext y
  obtain ⟨x, hx⟩ := exists_apply_eq_smul_of_le_annihilator_coker hcoker hf y
  have hx' : u' (a x) = f • b y := by
    rw [← comp_apply, hab, comp_apply, hx, map_smul]
  rw [comp_apply, comp_apply, fgMap_apply_of_apply_eq hker hcoker hf hg hx,
    fgMap_apply_of_apply_eq hker' hcoker' hf hg hx', map_smul]

/-- **Converse criterion.** If for all `f g ∈ I` there is `k` with `k ∘ v = (f * g) • id` and
`v ∘ k = (f * g) • id`, then kernel and cokernel of `v` are killed by `I * I`. -/
theorem mul_le_annihilator_ker_and_coker {v : P →ₗ[A] R}
    (hv : ∀ f ∈ I, ∀ g ∈ I, ∃ k : R →ₗ[A] P,
      k ∘ₗ v = (f * g) • LinearMap.id ∧ v ∘ₗ k = (f * g) • LinearMap.id) :
    I * I ≤ Module.annihilator A (ker v) ∧ I * I ≤ Module.annihilator A (R ⧸ range v) := by
  constructor
  · refine Submodule.mul_le.mpr fun f hf g hg => Module.mem_annihilator.mpr ?_
    rintro ⟨p, hp⟩
    obtain ⟨k, hk, -⟩ := hv f hf g hg
    have h := congrArg (· p) hk
    simp only [comp_apply, mem_ker.mp hp, map_zero, smul_apply, id_apply] at h
    ext
    simp [← h]
  · refine Submodule.mul_le.mpr fun f hf g hg => Module.mem_annihilator.mpr ?_
    intro r
    induction r using Submodule.Quotient.induction_on with
    | H r =>
      obtain ⟨k, -, hk⟩ := hv f hf g hg
      have h := congrArg (· r) hk
      simp only [comp_apply, smul_apply, id_apply] at h
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← h]
      exact mem_range_self v _

/-- The map `M ⧸ J • ⊤ →ₗ[A] N ⧸ J • ⊤` induced by `u` (reduction of `u` modulo `J`). -/
noncomputable abbrev mapQSmulTop (u : M →ₗ[A] N) (J : Ideal A) :
    M ⧸ (J • ⊤ : Submodule A M) →ₗ[A] N ⧸ (J • ⊤ : Submodule A N) :=
  Submodule.mapQ _ _ u (Submodule.smul_top_le_comap_smul_top J u)

include hker hcoker in
/-- If the kernel and cokernel of `u` are killed by `I`, then so are kernel and cokernel of
the reduction of `u` modulo any ideal `J`, by `I * I`. -/
theorem mul_le_annihilator_ker_and_coker_reduceModIdeal (J : Ideal A) :
    I * I ≤ Module.annihilator A (ker (u.mapQSmulTop J)) ∧
      I * I ≤ Module.annihilator A
        ((N ⧸ (J • ⊤ : Submodule A N)) ⧸ range (u.mapQSmulTop J)) := by
  refine mul_le_annihilator_ker_and_coker fun f hf g hg => ?_
  refine ⟨(fgMap u hker hcoker hf hg).mapQSmulTop J, ?_, ?_⟩
  · ext x
    simp [← comp_apply (fgMap u hker hcoker hf hg) u, fgMap_comp_self]
  · ext y
    simp [← comp_apply u (fgMap u hker hcoker hf hg), comp_fgMap]

end LinearMap
