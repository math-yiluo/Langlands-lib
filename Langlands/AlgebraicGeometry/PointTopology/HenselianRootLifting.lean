import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Root lifting over fields with Henselian norm valuation ring

A residually simple root at `1` of a polynomial `1 - X + (higher terms in the maximal ideal)`
over a Henselian local ring lifts to an actual root, although the polynomial need not be monic:
its reflection is monic and Hensel's property applies to it. Over a nontrivially normed
ultrametric field whose norm valuation ring is Henselian, this gives a root of norm at most
`‖c₀‖ / ‖c₁‖` whenever the coefficients satisfy the Newton-polygon inequalities
`‖cₖ‖ ‖c₀‖ ^ (k - 1) < ‖c₁‖ ^ k`, and hence roots near a simple root for every polynomial
family with continuous coefficients and bounded degree. No completeness is used.
-/

noncomputable section

open Filter Polynomial IsLocalRing
open scoped Topology

namespace Langlands.AlgebraicGeometry.PointTopology

namespace HenselianRoot

/-- In a Henselian local ring, a polynomial `1 - X + (higher terms in the maximal ideal)`
has a root, although it need not be monic. -/
theorem exists_isRoot_of_coeff {O : Type*} [CommRing O] [HenselianLocalRing O]
    (R : O[X]) (h0 : R.coeff 0 = 1) (h1 : R.coeff 1 = -1)
    (hk : ∀ k, 2 ≤ k → R.coeff k ∈ maximalIdeal O) :
    ∃ Z : O, R.IsRoot Z := by
  classical
  set N := R.natDegree with hN
  have hN1 : 1 ≤ N :=
    le_natDegree_of_ne_zero (by rw [h1]; exact neg_ne_zero.mpr one_ne_zero)
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  let Q : O[X] := reflect N R
  have hQmonic : Q.Monic := by
    apply monic_of_natDegree_le_of_coeff_eq_one N
    · exact natDegree_reflect_le.trans (by rw [← hN, max_self])
    · rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self, h0]
  have hRmap : R.map (residue O) = 1 - X := by
    ext k
    rw [coeff_map]
    rcases k with _ | _ | k
    · simp [h0]
    · simp [h1, coeff_one]
    · rw [(residue_eq_zero_iff _).mpr (hk _ (by omega))]
      simp [coeff_one, coeff_X]
  have hQmap : Q.map (residue O) = X ^ (M + 1) - X ^ M := by
    have hX : reflect N (X : (ResidueField O)[X]) = X ^ M := by
      have := reflect_monomial (R := ResidueField O) N 1
      rw [pow_one] at this
      rw [this, revAt_le hN1, hM, Nat.add_sub_cancel]
    show (reflect N R).map (residue O) = _
    rw [← reflect_map, hRmap, reflect_sub, reflect_one, hX, hM]
  have key (P : O[X]) (x : O) :
      residue O (P.eval x) = (P.map (residue O)).eval (residue O x) := by
    rw [eval_map, eval₂_hom]
  have hEval : Q.eval 1 ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff, key, hQmap, map_one]
    simp
  have hDer : IsUnit (Q.derivative.eval 1) := by
    rw [← residue_ne_zero_iff_isUnit, key, ← derivative_map, hQmap, map_one, derivative_sub,
      derivative_X_pow, derivative_X_pow]
    simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
    push_cast
    simp
  obtain ⟨V, hV, hV1⟩ := HenselianLocalRing.is_henselian Q hQmonic 1 hEval hDer
  have hVunit : IsUnit V := by
    rw [← residue_ne_zero_iff_isUnit]
    have hres := (residue_eq_zero_iff _).mpr hV1
    rw [map_sub, map_one, sub_eq_zero] at hres
    rw [hres]
    exact one_ne_zero
  obtain ⟨u, rfl⟩ := hVunit
  refine ⟨((u⁻¹ : Oˣ) : O), ?_⟩
  have hinv : ⅟((u⁻¹ : Oˣ) : O) = u := by
    rw [invOf_units, inv_inv]
  have h := (eval₂_reflect_eq_zero_iff (RingHom.id O) ((u⁻¹ : Oˣ) : O) N R le_rfl).mp
  rw [hinv] at h
  exact h hV

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

set_option hygiene false in
/-- The norm valuation ring of `K`. -/
local notation "𝒪" => (NormedField.valuation (K := K)).valuationSubring

/-- Membership in the norm valuation ring is the closed unit ball. -/
theorem mem_valuationSubring_iff (x : K) :
    x ∈ (NormedField.valuation (K := K)).valuationSubring ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe,
    coe_nnnorm, NNReal.coe_one]

/-- Units of the norm valuation ring are its elements of norm one. -/
theorem isUnit_valuationSubring_iff (x : (NormedField.valuation (K := K)).valuationSubring) :
    IsUnit x ↔ ‖(x : K)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h₁ : ‖((u : 𝒪) : K)‖ ≤ 1 := (mem_valuationSubring_iff _).mp (u : 𝒪).2
    have h₂ : ‖(((u⁻¹ : 𝒪ˣ) : 𝒪) : K)‖ ≤ 1 :=
      (mem_valuationSubring_iff _).mp ((u⁻¹ : 𝒪ˣ) : 𝒪).2
    have hmul : ‖((u : 𝒪) : K)‖ * ‖(((u⁻¹ : 𝒪ˣ) : 𝒪) : K)‖ = 1 := by
      rw [← norm_mul]
      have : ((u : 𝒪) : K) * (((u⁻¹ : 𝒪ˣ) : 𝒪) : K) = 1 := by
        change (((u : 𝒪) * ((u⁻¹ : 𝒪ˣ) : 𝒪) : 𝒪) : K) = ((1 : 𝒪) : K)
        rw [u.mul_inv]
      rw [this, norm_one]
    nlinarith [norm_nonneg ((u : 𝒪) : K), norm_nonneg (((u⁻¹ : 𝒪ˣ) : 𝒪) : K)]
  · intro hx
    have hx0 : (x : K) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx
      exact zero_ne_one hx
    have hinv : (x : K)⁻¹ ∈ (NormedField.valuation (K := K)).valuationSubring := by
      rw [mem_valuationSubring_iff, norm_inv, hx, inv_one]
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    change (x : K) * (x : K)⁻¹ = 1
    exact mul_inv_cancel₀ hx0

/-- The maximal ideal of the norm valuation ring is the open unit ball. -/
theorem mem_maximalIdeal_valuationSubring_iff
    (x : (NormedField.valuation (K := K)).valuationSubring) :
    x ∈ maximalIdeal (NormedField.valuation (K := K)).valuationSubring ↔ ‖(x : K)‖ < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_valuationSubring_iff]
  have := (mem_valuationSubring_iff (x : K)).mp x.2
  constructor
  · intro h
    exact lt_of_le_of_ne this h
  · intro h
    exact ne_of_lt h

variable [HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring]

/-- Over a field with Henselian norm valuation ring, a polynomial satisfying the strict
Newton-polygon inequalities at its first two coefficients has a root of norm at most
`‖c₀‖ / ‖c₁‖`. -/
theorem exists_root_norm_le (G : K[X]) (h1 : G.coeff 1 ≠ 0)
    (hk : ∀ k, 2 ≤ k → ‖G.coeff k‖ * ‖G.coeff 0‖ ^ (k - 1) < ‖G.coeff 1‖ ^ k) :
    ∃ y : K, G.eval y = 0 ∧ ‖y‖ ≤ ‖G.coeff 0‖ / ‖G.coeff 1‖ := by
  classical
  by_cases h0 : G.coeff 0 = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [← coeff_zero_eq_eval_zero, h0]
    · simp [h0]
  set c0 := G.coeff 0 with hc0
  set c1 := G.coeff 1 with hc1
  set e : K := -c0 / c1 with he
  let O := (NormedField.valuation (K := K)).valuationSubring
  let RK : K[X] := C c0⁻¹ * G.comp (C e * X)
  have hRK (k : ℕ) : RK.coeff k = c0⁻¹ * (G.coeff k * e ^ k) := by
    simp only [RK, coeff_C_mul, comp_C_mul_X_coeff]
  have hc0pos : 0 < ‖c0‖ := norm_pos_iff.mpr h0
  have hc1pos : 0 < ‖c1‖ := norm_pos_iff.mpr h1
  have hnorm (k : ℕ) (hk1 : 1 ≤ k) :
      ‖RK.coeff k‖ = ‖G.coeff k‖ * ‖c0‖ ^ (k - 1) / ‖c1‖ ^ k := by
    rw [hRK, norm_mul, norm_mul, norm_inv, norm_pow, he, norm_div, norm_neg, div_pow]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp
  have hcoef0 : RK.coeff 0 = 1 := by
    rw [hRK, pow_zero, mul_one, ← hc0, inv_mul_cancel₀ h0]
  have hcoef1 : RK.coeff 1 = -1 := by
    rw [hRK, pow_one, he, ← hc1]
    field_simp
  have hsmall (k : ℕ) (hk2 : 2 ≤ k) : ‖RK.coeff k‖ < 1 := by
    rw [hnorm k (by omega), div_lt_one (pow_pos hc1pos k)]
    exact hk k hk2
  have hmem (k : ℕ) : RK.coeff k ∈ O := by
    rw [mem_valuationSubring_iff]
    rcases k with _ | _ | k
    · rw [hcoef0, norm_one]
    · rw [hcoef1, norm_neg, norm_one]
    · exact (hsmall _ (by omega)).le
  have hlift : RK ∈ lifts (algebraMap O K) := by
    rw [lifts_iff_coeff_lifts]
    intro k
    exact ⟨⟨_, hmem k⟩, rfl⟩
  obtain ⟨R, hR⟩ := (mem_lifts RK).mp hlift
  have hRcoeff (k : ℕ) : ((R.coeff k : O) : K) = RK.coeff k := by
    rw [← hR, coeff_map]
    rfl
  obtain ⟨Z, hZ⟩ := exists_isRoot_of_coeff R
    (Subtype.ext (by rw [hRcoeff, hcoef0]; rfl))
    (Subtype.ext (by rw [hRcoeff, hcoef1]; rfl))
    (fun k hk2 => (mem_maximalIdeal_valuationSubring_iff _).mpr
      (by rw [hRcoeff]; exact hsmall k hk2))
  have hRKZ : RK.eval (Z : K) = 0 := by
    have : RK.eval (algebraMap O K Z) = algebraMap O K (R.eval Z) := by
      rw [← hR, eval_map, eval₂_hom]
    rw [show (Z : K) = algebraMap O K Z from rfl, this, hZ.eq_zero, map_zero]
  refine ⟨e * Z, ?_, ?_⟩
  · have hev : RK.eval (Z : K) = c0⁻¹ * G.eval (e * Z) := by
      simp only [RK, eval_mul, eval_C, eval_comp, eval_X]
    rw [hev] at hRKZ
    exact (mul_eq_zero.mp hRKZ).resolve_left (inv_ne_zero h0)
  · rw [norm_mul, he, norm_div, norm_neg]
    have hZ1 : ‖(Z : K)‖ ≤ 1 := (mem_valuationSubring_iff _).mp Z.2
    calc ‖c0‖ / ‖c1‖ * ‖(Z : K)‖ ≤ ‖c0‖ / ‖c1‖ * 1 := by gcongr
      _ = ‖c0‖ / ‖c1‖ := mul_one _

/-- For a polynomial family with continuous coefficients and bounded degree, a root `0` at
`t₀` with nonzero linear coefficient yields roots of norm less than any `ε > 0` nearby. -/
theorem eventually_exists_root {T : Type*} [TopologicalSpace T] {t₀ : T} (G : T → K[X])
    (N : ℕ) (hc : ∀ k, ContinuousAt (fun t => (G t).coeff k) t₀)
    (hN : ∀ t, (G t).natDegree ≤ N) (h0 : (G t₀).coeff 0 = 0) (h1 : (G t₀).coeff 1 ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∃ y : K, (G t).eval y = 0 ∧ ‖y‖ < ε := by
  have hne : ∀ᶠ t in 𝓝 t₀, (G t).coeff 1 ≠ 0 := (hc 1).eventually_ne h1
  have hfin : ∀ᶠ t in 𝓝 t₀, ∀ k ∈ Finset.Icc 2 N,
      ‖(G t).coeff k‖ * ‖(G t).coeff 0‖ ^ (k - 1) < ‖(G t).coeff 1‖ ^ k := by
    rw [eventually_all_finset]
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    apply ContinuousAt.eventually_lt
    · exact (hc k).norm.mul ((hc 0).norm.pow _)
    · exact (hc 1).norm.pow _
    · rw [h0, norm_zero, zero_pow (by omega), mul_zero]
      exact pow_pos (norm_pos_iff.mpr h1) k
  have hratio : ∀ᶠ t in 𝓝 t₀, ‖(G t).coeff 0‖ / ‖(G t).coeff 1‖ < ε := by
    apply ContinuousAt.eventually_lt ((hc 0).norm.div (hc 1).norm (norm_ne_zero_iff.mpr h1))
      continuousAt_const
    show ‖(G t₀).coeff 0‖ / ‖(G t₀).coeff 1‖ < ε
    rw [h0, norm_zero, zero_div]
    exact hε
  filter_upwards [hne, hfin, hratio] with t hne hfin hratio
  obtain ⟨y, hy, hyn⟩ := exists_root_norm_le (G t) hne (by
    intro k hk2
    by_cases hkN : k ≤ N
    · exact hfin k (Finset.mem_Icc.mpr ⟨hk2, hkN⟩)
    · rw [coeff_eq_zero_of_natDegree_lt ((hN t).trans_lt (not_le.mp hkN)), norm_zero,
        zero_mul]
      exact pow_pos (norm_pos_iff.mpr hne) k)
  exact ⟨y, hy, hyn.trans_lt hratio⟩

end HenselianRoot

end Langlands.AlgebraicGeometry.PointTopology
