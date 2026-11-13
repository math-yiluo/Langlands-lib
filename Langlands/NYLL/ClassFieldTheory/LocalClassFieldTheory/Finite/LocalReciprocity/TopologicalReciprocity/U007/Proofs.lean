/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 65, 13 November 2026: prove M257.007
`localNormSubgroup_isOpen` from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
TopologicalReciprocity.lean (lines 215–331 at
fbd320cd8b1b06487c58227e92eb135794267709) against the published target
`localNormSubgroup_isOpenStatement`. The theorem name, binders and docstring
are retained; namespaces are prefixed with Langlands.NYLL. The original proof
(spectral-norm local-field structures on L followed by the M257.006 compatible
openness theorem) is replaced by a direct elementary proof: an element of
nonzero trace, the norm as a determinant, and Newton's method over the complete
valuation ring of K. The helper `exists_root_of_isAdicComplete` adapts the
proof of Mathlib's `IsAdicComplete.henselianRing`
(Mathlib/RingTheory/Henselian.lean, Copyright (c) 2021 Johan Commelin,
Apache 2.0), which does not use its monicity hypothesis.
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U006.Statements
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Openness of the norm subgroup of a finite Galois extension of a local field

For a finite Galois extension `L/K` of a nonarchimedean local field `K`, the image of the norm
`Lˣ → Kˣ` is open in `Kˣ`. The proof is elementary: for `c : L` of nonzero trace, the
polynomial `t ↦ N_{L/K}(1 + t c)` (after rescaling to integral coefficients) has constant term
`1` and nonzero linear term, so by Newton's method over the complete discrete valuation ring
`𝒪[K]` its values on `𝒪[K]` cover a coset `1 + ϖ 𝒪[K]` with `ϖ ≠ 0`.
-/

open Polynomial IsLocalRing
open scoped Ring

namespace Langlands.NYLL.PortInternal.M257.D007

/-- Newton's method over an `I`-adically complete ring, without a monicity hypothesis. -/
theorem exists_root_of_isAdicComplete {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
  let f' := derivative f
  let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
    intro n
    simp only [c]
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => ?_
    rw [hc, sub_eq_add_neg, ← add_zero a₀]
    refine ih.add ?_
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine I.mul_mem_right _ ?_
    rw [← SModEq.zero] at h₁ ⊢
    exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
    | succ n ih => ?_
    rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
      add_neg_cancel_comm]
    rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
      Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
    swap
    · intro i
      rw [zero_mul]
    refine Ideal.add_mem _ ?_ ?_
    · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
        taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
        mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
      exact Ideal.zero_mem _
    · refine Submodule.sum_mem _ ?_
      simp only [Finset.mem_Ico]
      rintro i ⟨h2i, _⟩
      have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
      rw [pow_mul']
      exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih => ?_
    rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
    refine ih.add ?_
    symm
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
    rw [add_assoc]
    exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

/-- Coefficients of `g(aX)`. -/
theorem coeff_comp_C_mul_X {R : Type*} [CommRing R] (g : R[X]) (a : R) (j : ℕ) :
    (g.comp (C a * X)).coeff j = a ^ j * g.coeff j := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial n r =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow,
      ← mul_assoc, ← C_mul, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

/-- Over a complete discrete valuation ring, a polynomial with constant term `1` and
nonzero linear coefficient attains every value in a fixed nontrivial coset `1 + ϖ R`. -/
theorem exists_eval_eq_one_add {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (maximalIdeal R) R]
    (g : R[X]) (h0 : g.eval 0 = 1) (h1 : g.coeff 1 ≠ 0) :
    ∃ ϖ : R, ϖ ≠ 0 ∧ ∀ z : R, ∃ t : R, g.eval t = 1 + ϖ * z := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨k, u, hτ⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h1 hπ
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπm : π ∈ maximalIdeal R := hπ.not_isUnit
  refine ⟨π ^ (2 * k + 1), pow_ne_zero _ hπ0, fun z => ?_⟩
  set ϖ : R := π ^ (2 * k + 1) with hϖ
  let Q : R[X] := g.comp (C (π ^ (k + 1)) * X) - C (1 + ϖ * z)
  have hQcoeff : ∀ j, Q.coeff j =
      (π ^ (k + 1)) ^ j * g.coeff j - if j = 0 then 1 + ϖ * z else 0 := by
    intro j
    simp only [Q, coeff_sub, coeff_comp_C_mul_X, coeff_C]
  have hg0 : g.coeff 0 = 1 := by rw [coeff_zero_eq_eval_zero, h0]
  have hQ0 : Q.coeff 0 = ϖ * (-z) := by
    rw [hQcoeff]; simp [hg0]
  have hQ1 : Q.coeff 1 = ϖ * u := by
    rw [hQcoeff, hτ, hϖ]; simp only [one_ne_zero, ite_false, sub_zero, pow_one]; ring
  have hQj : ∀ j, 2 ≤ j → Q.coeff j = ϖ * (π ^ ((k + 1) * j - (2 * k + 1)) * g.coeff j) := by
    intro j hj
    rw [hQcoeff, ite_eq_right (by omega), sub_zero, hϖ, ← mul_assoc, ← pow_add, ← pow_mul]
    congr 2
    have : 2 * k + 1 ≤ (k + 1) * j := by nlinarith
    omega
  have hdvd : C ϖ ∣ Q := by
    rw [C_dvd_iff_dvd_coeff]
    intro j
    rcases j with _ | _ | j
    · exact ⟨_, hQ0⟩
    · exact ⟨_, hQ1⟩
    · exact ⟨_, hQj _ (by omega)⟩
  obtain ⟨h, hQh⟩ := hdvd
  have hϖ0 : ϖ ≠ 0 := pow_ne_zero _ hπ0
  have hhcoeff : ∀ j, ϖ * h.coeff j = Q.coeff j := by
    intro j; rw [hQh, coeff_C_mul]
  have hh0 : h.coeff 0 = -z :=
    mul_left_cancel₀ hϖ0 ((hhcoeff 0).trans hQ0)
  have hh1 : h.coeff 1 = u :=
    mul_left_cancel₀ hϖ0 ((hhcoeff 1).trans hQ1)
  have hhj : ∀ j, 2 ≤ j → h.coeff j ∈ maximalIdeal R := by
    intro j hj
    rw [mul_left_cancel₀ hϖ0 ((hhcoeff j).trans (hQj j hj))]
    apply Ideal.mul_mem_right
    apply Ideal.pow_mem_of_mem _ hπm
    have : 2 * k + 1 < (k + 1) * j := by nlinarith
    omega
  have hmap : h.map (residue R) = C (residue R (-z)) + C (residue R (u : R)) * X := by
    ext j
    rw [coeff_map, coeff_add, coeff_C, coeff_C_mul_X]
    rcases j with _ | _ | j
    · simp [hh0]
    · simp [hh1]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), add_zero,
        (residue_eq_zero_iff _).2 (hhj _ (by omega))]
  let a₀ : R := z * ↑u⁻¹
  have hroot : h.eval a₀ ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, ← eval₂_at_apply, ← eval_map, hmap]
    simp only [eval_add, eval_C, eval_mul, eval_X, a₀]
    have hz : -z + (u : R) * (z * ↑u⁻¹) = 0 := by
      rw [mul_left_comm, Units.mul_inv, mul_one, neg_add_cancel]
    rw [← map_mul, ← map_add, hz, map_zero]
  have hsimple : IsUnit (Ideal.Quotient.mk (maximalIdeal R) (h.derivative.eval a₀)) := by
    change IsUnit (residue R (h.derivative.eval a₀))
    rw [← eval₂_at_apply, ← eval_map, ← derivative_map, hmap]
    simp only [derivative_add, derivative_C, derivative_mul, derivative_X, zero_add, mul_one,
      zero_mul, eval_C]
    exact u.isUnit.map _
  obtain ⟨s, hs, -⟩ := exists_root_of_isAdicComplete (maximalIdeal R) h a₀ hroot hsimple
  refine ⟨π ^ (k + 1) * s, ?_⟩
  have hQs : Q.eval s = 0 := by rw [hQh, eval_mul, hs.eq_zero, mul_zero]
  simp only [Q, eval_sub, eval_comp, eval_mul, eval_C, eval_X] at hQs
  exact sub_eq_zero.mp hQs

/-- Any finite family in a valued field has a common nonzero integral multiplier. -/
theorem exists_mul_mem_integer {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) {ι : Type*} (s : Finset ι) (f : ι → K) :
    ∃ β : K, β ≠ 0 ∧ β ∈ v.integer ∧ ∀ i ∈ s, β * f i ∈ v.integer := by
  classical
  have key : ∀ x : K, ∃ d : K, d ≠ 0 ∧ d ∈ v.integer ∧ d * x ∈ v.integer := by
    intro x
    by_cases hx : v x ≤ 1
    · exact ⟨1, one_ne_zero, v.integer.one_mem, by rwa [one_mul]⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      refine ⟨x⁻¹, inv_ne_zero hx0, ?_, ?_⟩
      · rw [Valuation.mem_integer_iff, map_inv₀]
        exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hx))
      · rw [inv_mul_cancel₀ hx0]
        exact v.integer.one_mem
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, v.integer.one_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨β, hβ0, hβ, hβs⟩ := ih
    obtain ⟨d, hd0, hd, hdx⟩ := key (β * f a)
    refine ⟨d * β, mul_ne_zero hd0 hβ0, v.integer.mul_mem hd hβ, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [mul_assoc]
      exact hdx
    · rw [mul_assoc]
      exact v.integer.mul_mem hd (hβs i hi)

end Langlands.NYLL.PortInternal.M257.D007

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory ValuativeRel Topology
open scoped ValuativeRel

/-- The norm subgroup of a finite Galois extension of a nonarchimedean local
field is open in the native topology of the base-field unit group. -/
theorem localNormSubgroup_isOpen
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : localNormSubgroup_isOpenStatement K L := by
  classical
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨c, hc⟩ : ∃ c : L, Algebra.trace K L c ≠ 0 := by
    by_contra! h
    exact Algebra.trace_ne_zero K L (LinearMap.ext h)
  let b := Module.finBasis K L
  let M := Algebra.leftMulMatrix b c
  obtain ⟨β, hβ0, -, hβM⟩ := PortInternal.M257.D007.exists_mul_mem_integer (valuation K)
    (Finset.univ : Finset (Fin (Module.finrank K L) × Fin (Module.finrank K L)))
    (fun p => M p.1 p.2)
  let A : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) 𝒪[K] :=
    fun i j => ⟨β * M i j, hβM (i, j) (Finset.mem_univ _)⟩
  let g : 𝒪[K][X] := Matrix.charpolyRev (-A)
  have hg0 : g.eval 0 = 1 := Matrix.eval_charpolyRev
  have htr : ((Matrix.trace A : 𝒪[K]) : K) = β * Algebra.trace K L c := by
    rw [Algebra.trace_eq_matrix_trace b]
    simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, A, M]
    push_cast
    rfl
  have hg1 : g.coeff 1 ≠ 0 := by
    rw [Matrix.coeff_charpolyRev_eq_neg_trace, Matrix.trace_neg, neg_neg]
    intro h
    rw [h] at htr
    exact mul_ne_zero hβ0 hc (by simpa using htr.symm)
  have hgN : ∀ t : 𝒪[K], ((g.eval t : 𝒪[K]) : K) = Algebra.norm K (1 + ((t : K) * β) • c) := by
    intro t
    let φ : 𝒪[K][X] →+* K := (𝒪[K]).subtype.comp (Polynomial.evalRingHom t)
    have hφ : φ.mapMatrix (1 - (X : 𝒪[K][X]) • (-A).map C) =
        Algebra.leftMulMatrix b (1 + ((t : K) * β) • c) := by
      rw [map_add, map_one, map_smul]
      ext i j
      have hA : ((A i j : 𝒪[K]) : K) = β * M i j := rfl
      simp only [φ, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.one_apply,
        smul_eq_mul, map_sub, map_mul, map_neg, RingHom.comp_apply, coe_evalRingHom, eval_X,
        eval_C, Subring.coe_subtype, hA]
      split_ifs <;> simp [M] <;> ring
    rw [Algebra.norm_eq_matrix_det b, ← hφ, ← RingHom.map_det]
    rfl
  obtain ⟨ϖ, hϖ0, hϖ⟩ := PortInternal.M257.D007.exists_eval_eq_one_add g hg0 hg1
  have hϖK : (ϖ : K) ≠ 0 := fun h => hϖ0 (Subtype.ext h)
  have hvϖ : valuation K (ϖ : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖK
  have hsub : ∀ y : Kˣ, valuation K ((y : K) - 1) < valuation K (ϖ : K) →
      y ∈ localNormSubgroup K L := by
    intro y hy
    have hz : ((y : K) - 1) / ϖ ∈ 𝒪[K] := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact (div_le_one₀ (zero_lt_iff.mpr hvϖ)).mpr hy.le
    obtain ⟨t, ht⟩ := hϖ ⟨_, hz⟩
    have hyN : (y : K) = Algebra.norm K (1 + ((t : K) * β) • c) := by
      rw [← hgN, ht]
      push_cast
      field_simp
      ring
    have hx0 : (1 + ((t : K) * β) • c) ≠ 0 := by
      rw [← Algebra.norm_ne_zero_iff (R := K), ← hyN]
      exact y.ne_zero
    show y ∈ (normUnits K L).range
    exact ⟨Units.mk0 _ hx0, Units.ext hyN.symm⟩
  have hS : {x : K | valuation K (x - 1) < valuation K (ϖ : K)} ∈ 𝓝 (1 : K) := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨Units.mk0 _ hvϖ, fun x hx => hx⟩
  have hU := (Units.continuous_val (M := K)).continuousAt (x := (1 : Kˣ)) |>.preimage_mem_nhds
    (by simpa using hS)
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset hU fun y hy => hsub y hy)

end Langlands.NYLL.LocalClassFieldTheory
