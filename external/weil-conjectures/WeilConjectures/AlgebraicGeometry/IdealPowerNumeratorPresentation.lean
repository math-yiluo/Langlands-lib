/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Span
import WeilConjectures.AlgebraicGeometry.GeneralIdealPowerAffineSections
import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # A linear presentation of ideal-power numerators

Source: Stacks Project, Properties, Lemma 01PM, monomial construction in its proof.
(blueprint: lem-weil-pbc-ideal-power-numerator-presentation).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

private theorem span_generator_powers_bound
    {R : Type u} [CommRing R] (t k : ℕ) (g : Fin t → R) :
    Ideal.span (Set.range g) ^ (t * k + 1) ≤
      Ideal.span (Set.range (fun i ↦ g i ^ k)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hr : Set.range g = insert (g 0) (Set.range (fun i : Fin t ↦ g i.succ)) := by
      ext r
      simp only [Set.mem_range, Set.mem_insert_iff]
      constructor
      · rintro ⟨i, rfl⟩
        cases i using Fin.cases with
        | zero => exact Or.inl rfl
        | succ i => exact Or.inr ⟨i, rfl⟩
      · rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨0, rfl⟩
        · exact ⟨i.succ, rfl⟩
    rw [hr, Ideal.span_insert]
    have hn : (t + 1) * k + 1 = k + (t * k + 1) := by rw [Nat.add_mul]; omega
    rw [hn]
    apply (Ideal.sup_pow_add_le_pow_sup_pow).trans
    apply sup_le
    · rw [Ideal.span_singleton_pow]
      exact Ideal.span_mono (by intro r hr; rcases hr with rfl; exact ⟨0, rfl⟩)
    · exact (ih (fun i : Fin t ↦ g i.succ)).trans
        (Ideal.span_mono (by rintro r ⟨i, rfl⟩; exact ⟨i.succ, rfl⟩))

set_option backward.isDefEq.respectTransparency false in
/-- Compatible numerators give a surjective linear presentation of a power of the ideal.

Source: Stacks Project, Properties, Lemma 01PM, paragraphs defining the exponent
and assigning an image to each degree-d monomial; Lemma 01PQ, affine reduction.
(blueprint: lem-weil-pbc-ideal-power-numerator-presentation).

Proof: Put R=O_X(V), M=F(V), J=(g_i), and H=(g_i^k). The existing affine-power
calculation proves that P_n is quasi-coherent and has section image J^n. We use
the convenient, nonminimal exponent n=t*k+1. Induct on the number of generators:
for no generators J^1=0; after adjoining g_0, the ideal inequality
(A+B)^(k+(t*k+1)) <= A^k+B^(t*k+1), the singleton-power formula, and induction
give J^n <= H. This uses Mathlib's sup_pow_add_le_pow_sup_pow and
span_singleton_pow, so explicit monomial enumeration is unnecessary.
Define E as the submodule of P_n(V) times M of pairs (b,m) satisfying
 g_i^k*m=j_n(b)*x_i for every i. Let p and q be its projections. Induction on
membership in H shows that every r in H has such a numerator m: for r=g_l^k
use x_l and the cross relation; extend using zero, addition, and scalar
multiplication. Applying this to j_n(b) proves p surjective. The scalar identity
for q is the defining equation of E. This construction works also for t=0,
k=0, J=R, and the zero ring. The graph is an actual submodule defined by these
linear equations; no data is chosen from an unproved existence theorem. -/
theorem ideal_power_numerator_presentation
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι] [I.IsQuasicoherent]
    (F : X.Modules) (V : X.affineOpens) (t k : ℕ)
    (g : Fin t → Γ(X, V.1)) (x : Fin t → Γ(F, V.1))
    (hg : (LinearMap.range (ι.val.app (op V.1)).hom : Ideal Γ(X, V.1)) =
      Ideal.span (Set.range g))
    (hx : ∀ i j, g j ^ k • x i = g i ^ k • x j) :
    let n := t * k + 1
    ((idealSheafPower ι n).1).IsQuasicoherent ∧
    (LinearMap.range ((idealSheafPower ι n).2.val.app (op V.1)).hom :
      Ideal Γ(X, V.1)) ≤ Ideal.span (Set.range (fun i ↦ g i ^ k)) ∧
    ∃ (E : ModuleCat.{u} Γ(X, V.1))
      (p : E →ₗ[Γ(X, V.1)] Γ((idealSheafPower ι n).1, V.1))
      (q : E →ₗ[Γ(X, V.1)] Γ(F, V.1)),
      Function.Surjective p ∧ ∀ (i : Fin t) (z : E),
        g i ^ k • q z =
          (show Γ(X, V.1) from (idealSheafPower ι n).2.app V.1 (p z)) • x i := by
  classical
  let n := t * k + 1
  obtain ⟨hP, hJ⟩ := general_ideal_power_affine_sections ι n
  have hrange : (LinearMap.range
      ((idealSheafPower ι n).2.val.app (op V.1)).hom : Ideal Γ(X, V.1)) ≤
      Ideal.span (Set.range (fun i ↦ g i ^ k)) := by
    rw [hJ V, hg]
    exact span_generator_powers_bound t k g
  let j : Γ((idealSheafPower ι n).1, V.1) →ₗ[Γ(X, V.1)] Γ(X, V.1) :=
    ((idealSheafPower ι n).2.val.app (op V.1)).hom
  let L : Submodule Γ(X, V.1) (Γ((idealSheafPower ι n).1, V.1) × Γ(F, V.1)) :=
    { carrier := {z | ∀ i, g i ^ k • z.2 = j z.1 • x i}
      zero_mem' := by simp
      add_mem' := by
        intro z w hz hw i
        simp only [Prod.fst_add, Prod.snd_add, smul_add, map_add, add_smul, hz i, hw i]
      smul_mem' := by
        intro r z hz i
        simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.map_smul,
          smul_comm (g i ^ k) r, hz i, smul_smul, smul_eq_mul] }
  let p := (LinearMap.fst Γ(X, V.1) Γ((idealSheafPower ι n).1, V.1)
    Γ(F, V.1)).comp L.subtype
  let q := (LinearMap.snd Γ(X, V.1) Γ((idealSheafPower ι n).1, V.1)
    Γ(F, V.1)).comp L.subtype
  have hp : Function.Surjective p := by
    intro b
    have hb : j b ∈ Ideal.span (Set.range (fun i ↦ g i ^ k)) := hrange ⟨b, rfl⟩
    have hex : ∀ r ∈ Ideal.span (Set.range (fun i ↦ g i ^ k)),
        ∃ m : Γ(F, V.1), ∀ i, g i ^ k • m = r • x i := by
      intro r hr
      induction hr using Submodule.span_induction with
      | mem r hr =>
        obtain ⟨l, rfl⟩ := hr
        exact ⟨x l, fun i ↦ hx l i⟩
      | zero => exact ⟨0, by simp⟩
      | add r s hr hs ihr ihs =>
        obtain ⟨m, hm⟩ := ihr
        obtain ⟨m', hm'⟩ := ihs
        exact ⟨m + m', by simp [smul_add, add_smul, hm, hm']⟩
      | smul r s hs ih =>
        obtain ⟨m, hm⟩ := ih
        refine ⟨r • m, fun i ↦ ?_⟩
        rw [smul_comm, hm, smul_smul]
        rfl
    obtain ⟨m, hm⟩ := hex (j b) hb
    exact ⟨⟨(b, m), hm⟩, rfl⟩
  refine ⟨hP, hrange, ModuleCat.of Γ(X, V.1) L, p, q, hp, ?_⟩
  intro i z
  exact z.property i

end AlgebraicGeometry.Scheme
