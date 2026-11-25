/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Nonconstant p-basis coefficients of an element with zero differential

Source: Stacks Project, More on Algebra, Tags 07P1 and 07P2.
(blueprint: lem-weil-pbc-p-basis-zero-differential-coefficients).
-/

@[expose] public section

universe u v w

namespace KaehlerDifferential

private theorem euler_monomial
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {I : Type w} [DecidableEq I] (t : I → K) (i : I) (d : Derivation k K K)
    (ht : ∀ j, d (t j) = if i = j then 1 else 0) (f : I →₀ ℕ) :
    t i * d (f.prod (fun j n ↦ t j ^ n)) = (f i : K) * f.prod (fun j n ↦ t j ^ n) := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | @single_add j n f hj hn ih =>
    rw [Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)]
    simp only [Finsupp.prod_single_index, pow_zero, Finsupp.add_apply]
    rw [d.leibniz, d.leibniz_pow, ht]
    by_cases hij : i = j
    · subst j
      have hfi : f i = 0 := Finsupp.notMem_support_iff.mp hj
      simp only [ite_true, Finsupp.single_eq_same, hfi, add_zero, smul_eq_mul,
        nsmul_eq_mul, mul_one]
      have hpow : t i * t i ^ (n - 1) = t i ^ n := by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
      have hz : t i * d (f.prod (fun j n ↦ t j ^ n)) = 0 := by simpa [hfi] using ih
      calc
        _ = t i ^ n * (t i * d (f.prod (fun j n ↦ t j ^ n))) +
            (n : K) * (t i * t i ^ (n - 1)) * f.prod (fun j n ↦ t j ^ n) := by ring
        _ = _ := by rw [hz, hpow]; ring
    · simp only [ite_eq_right hij, mul_zero, nsmul_zero, add_zero,
        Finsupp.single_eq_of_ne hij, zero_add, smul_eq_mul]
      calc
        _ = t j ^ n * (t i * d (f.prod (fun j n ↦ t j ^ n))) := by ring
        _ = _ := by rw [ih]; ring

/-- If the differential of an element vanishes, all its nonconstant p-basis coordinates
vanish when the differentials of the p-basis form the given basis.
Source: Stacks Project, More on Algebra, Tag 07P2, proof of (2) implies (1), and
step 4 of lem-weil-pbc-differential-zero-iff-pth-power.
(blueprint: lem-weil-pbc-p-basis-zero-differential-coefficients)

Proof:
Put B = kK^p and choose i with E i > 0. Compose the universal derivation with
the i-th coordinate of the given differential basis to get a k-derivation d_i
with d_i(t_j) = delta_ij. It kills B: it kills k and p-th powers, and the
Leibniz and inverse rules show that the killed elements are closed under the
operations used to generate B. Therefore L_i(x) = t_i * d_i(x) is B-linear.
Induction on the finite support of F, using Leibniz, proves the Euler identity
L_i(t^F) = (F i) * t^F. This is the source's partial-derivative calculation
multiplied by t_i, so no reindexing of reduced monomials is necessary.
Evaluate the B-linear maps coord_E composed with L_i and (E i) * coord_E on
every monomial basis vector: both give (E i) times the E-th coordinate.
Basis extensionality makes these maps equal. Since D(a) = 0, L_i(a) = 0,
hence (E i) * coord_E(a) = 0. The scalar E i is nonzero because 0 < E i < p
and K has characteristic p; cancel it to obtain coord_E(a) = 0.
The argument works for infinite I because monomials have finite support.
For empty I, no nonzero E exists, so the assertion is vacuous. No perfection
hypothesis on k is needed: every k-derivation kills B. -/
theorem pBasis_repr_eq_zero_of_D_eq_zero
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP K p]
    {I : Type w} (t : I → K)
    (b : Module.Basis {E : I →₀ ℕ // ∀ i : I, E i < p}
      (IntermediateField.adjoin k (Set.range (fun x : K ↦ x ^ p))) K)
    (hb : ∀ E, b E = E.val.prod (fun i e ↦ t i ^ e))
    (bd : Module.Basis I K (KaehlerDifferential k K))
    (hbd : ∀ i, bd i = D k K (t i))
    (a : K) (ha : D k K a = 0)
    (E : {E : I →₀ ℕ // ∀ i : I, E i < p}) (hE : E.val ≠ 0) :
    b.repr a E = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, E.val i ≠ 0 := by
    by_contra h
    apply hE
    ext j
    simpa using not_exists.mp h j
  let d : Derivation k K K := (bd.coord i).compDer (D k K)
  have ht : ∀ j, d (t j) = if i = j then 1 else 0 := by
    intro j
    change bd.repr (D k K (t j)) i = _
    rw [← hbd, bd.repr_self]
    simp [Finsupp.single_apply, eq_comm]
  let B := IntermediateField.adjoin k (Set.range (fun x : K ↦ x ^ p))
  have hk : ∀ c : B, d (c : K) = 0 := by
    suffices h : ∀ x : K, x ∈ B → d x = 0 from fun c ↦ h c c.property
    intro x hx
    change x ∈ IntermediateField.adjoin k _ at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      rw [d.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero]
      simp
    | algebraMap x => exact d.map_algebraMap x
    | add x y hx hy hdx hdy => simp [hdx, hdy]
    | inv x hx hdx => rw [d.leibniz_inv, hdx, smul_zero]
    | mul x y hx hy hdx hdy => simp [hdx, hdy]
  let L : K →ₗ[B] K :=
    { toFun := fun x ↦ t i * d x
      map_add' := by intros; simp [mul_add]
      map_smul' := by
        intro c x
        change t i * d ((c : K) * x) = (c : K) * (t i * d x)
        rw [d.leibniz, hk c]
        simp only [smul_eq_mul, mul_zero, add_zero]
        ring }
  have hL : ∀ F, L (b F) = (F.val i : B) • b F := by
    intro F
    change t i * d (b F) = _
    rw [hb]
    simpa only [Algebra.smul_def, map_natCast] using euler_monomial t i d ht F.val
  have hcoord : (b.coord E).comp L = (E.val i : B) • b.coord E := by
    apply b.ext
    intro F
    simp only [LinearMap.comp_apply, hL, map_smul, LinearMap.smul_apply,
      Module.Basis.coord_apply, b.repr_self]
    by_cases h : F = E
    · subst F
      rfl
    · simp [h]
  have hLa : L a = 0 := by
    change t i * bd.coord i (D k K a) = 0
    rw [ha, map_zero, mul_zero]
  have hz : (E.val i : B) * b.repr a E = 0 := by
    have h := LinearMap.congr_fun hcoord a
    simpa only [LinearMap.comp_apply, hLa, map_zero, LinearMap.smul_apply,
      Module.Basis.coord_apply, smul_eq_mul] using h.symm
  have hni : (E.val i : B) ≠ 0 := by
    intro h
    have h' : (E.val i : K) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg (algebraMap B K) h
    have hdvd := (CharP.cast_eq_zero_iff K p (E.val i)).mp h'
    exact hi (Nat.eq_zero_of_dvd_of_lt hdvd (E.property i))
  exact (mul_eq_zero.mp hz).resolve_left hni

end KaehlerDifferential
