import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Langlands.ClassFieldTheory.Local.SeparableInertiaNormCyclic

/-! # Unit norm surjectivity for a finite Galois extension

Let `M / E` be a finite Galois extension and let `w` be a real valuation on `M` that is invariant
under `Gal(M/E)`. Assume that `w` satisfies Hensel's lemma for simple roots on `M`, that its
values on integral elements are discrete, that every integral element of `M` is congruent modulo
the maximal ideal to an integral element of `E`, that root finding modulo the maximal ideal holds
over `E`, and that integers prime to a prime `p` have value `1`. Then every unit of `E` is the
norm of a unit of `M`.

The hypotheses descend from `M` to every intermediate field: simple-root Hensel lifting descends
by Galois invariance and uniqueness of Hensel roots, root finding by approximating coefficients,
and discreteness yields a uniformizer. The proof takes a Sylow `p`-subgroup `P` of `Gal(M/E)`.
Over `B = M ^ P` the index `[B : E]` is prime to `p`, so a unit of `E` is an `[B : E]`-th power
of a unit of `E` by Hensel's lemma. Over `B` the extension `M / B` is a tower of Galois
extensions of degree `p`, each handled by the cyclic step.
-/

noncomputable section

open Polynomial Finset Module
open scoped NNReal

namespace Langlands.ClassFieldTheory.Local.SeparableInertiaNorm

section Field

variable {K : Type*} [Field K] {v : Valuation K ℝ≥0}

theorem IntPoly.derivative {f : K[X]} (hf : IntPoly v f) : IntPoly v (derivative f) := by
  intro i
  rw [coeff_derivative, map_mul]
  have := val_natCast_le_one (v := v) (i + 1)
  rw [Nat.cast_succ] at this
  exact mul_le_one' (hf _) this

theorem IntPoly.hasseDeriv {f : K[X]} (hf : IntPoly v f) (k : ℕ) :
    IntPoly v (hasseDeriv k f) := by
  intro i
  rw [hasseDeriv_coeff, map_mul]
  exact mul_le_one' (val_natCast_le_one _) (hf _)

/-- An integral polynomial is `1`-Lipschitz on integral elements. -/
theorem val_eval_sub_le {f : K[X]} (hf : IntPoly v f) {a b : K} (ha : v a ≤ 1) (hb : v b ≤ 1) :
    v (f.eval a - f.eval b) ≤ v (a - b) := by
  rw [eval_eq_sum_range, eval_eq_sum_range, ← sum_sub_distrib]
  refine v.map_sum_le fun i _ => ?_
  rw [← mul_sub, ← geom_sum₂_mul, map_mul, map_mul]
  have hs : v (∑ j ∈ range i, a ^ j * b ^ (i - 1 - j)) ≤ 1 :=
    v.map_sum_le fun j _ => by
      rw [map_mul, map_pow, map_pow]
      exact mul_le_one' (pow_le_one' ha _) (pow_le_one' hb _)
  calc v (f.coeff i) * (v (∑ j ∈ range i, a ^ j * b ^ (i - 1 - j)) * v (a - b))
      ≤ 1 * (1 * v (a - b)) := mul_le_mul' (hf i) (mul_le_mul' hs le_rfl)
    _ = v (a - b) := by rw [one_mul, one_mul]

/-- Uniqueness of simple roots: two roots of an integral polynomial that are congruent modulo
the maximal ideal coincide when the derivative at one of them is a unit. -/
theorem eq_of_eval_eq_zero {f : K[X]} (hf : IntPoly v f) {a b : K} (ha : v a ≤ 1)
    (hfa : f.eval a = 0) (hfb : f.eval b = 0) (hab : v (b - a) < 1)
    (hd : v (f.derivative.eval a) = 1) : b = a := by
  by_contra hne
  set y := b - a with hy
  have hy0 : y ≠ 0 := sub_ne_zero.mpr hne
  set t := taylor a f with ht
  have htc : ∀ n, v (t.coeff n) ≤ 1 := fun n => by
    rw [ht, taylor_coeff]
    exact val_eval_le_one (hf.hasseDeriv n) ha
  set N := t.natDegree
  have hev : t.eval y = 0 := by rw [ht, taylor_eval, hy, sub_add_cancel, hfb]
  have hsplit : t.eval y = t.coeff 0 + t.coeff 1 * y +
      y * ∑ k ∈ Ico 2 (N + 2), t.coeff k * y ^ (k - 1) := by
    rw [eval_eq_sum_range' (n := N + 2) (by omega), range_eq_Ico,
      sum_eq_sum_Ico_succ_bot (by omega : 0 < N + 2),
      sum_eq_sum_Ico_succ_bot (by omega : 0 + 1 < N + 2), mul_sum, pow_zero, mul_one, zero_add,
      pow_one, ← add_assoc]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    have hk := (mem_Ico.mp hk).1
    rw [show y ^ k = y * y ^ (k - 1) by rw [← pow_succ']; congr 1; omega]
    ring
  rw [hsplit, ht, taylor_coeff_zero, taylor_coeff_one, hfa, zero_add, ← ht, ← mul_comm y,
    ← mul_add] at hev
  have hkey := (mul_eq_zero.mp hev).resolve_left hy0
  have hlt : v (∑ k ∈ Ico 2 (N + 2), t.coeff k * y ^ (k - 1)) < 1 :=
    v.map_sum_lt one_ne_zero fun k hk => by
      have hk := (mem_Ico.mp hk).1
      rw [map_mul, map_pow]
      exact (mul_le_of_le_one_left zero_le (htc k)).trans_lt
        (pow_lt_one₀ zero_le hab (by omega))
  rw [eq_neg_of_add_eq_zero_left hkey, Valuation.map_neg] at hd
  exact hlt.ne hd

/-- Galois descent of simple-root Hensel lifting along `K → L`. -/
theorem valHensel_comap {L : Type*} [Field L] [Algebra K L] {w : Valuation L ℝ≥0}
    (hL : ValHensel w) (hinv : ∀ (σ : L ≃ₐ[K] L) (x : L), w (σ x) = w x)
    (hfix : ∀ x : L, (∀ σ : L ≃ₐ[K] L, σ x = x) → x ∈ Set.range (algebraMap K L)) :
    ValHensel (w.comap (algebraMap K L)) := by
  intro f hmon hint a₀ ha₀ hev hder
  simp only [Valuation.comap_apply] at hint ha₀ hev hder
  set g := f.map (algebraMap K L) with hg
  have hgint : IntPoly w g := fun i => by rw [hg, coeff_map]; exact hint i
  have hgev : ∀ x : K, g.eval (algebraMap K L x) = algebraMap K L (f.eval x) := fun x => by
    rw [hg, eval_map, eval₂_hom]
  have hgdev : g.derivative.eval (algebraMap K L a₀) = algebraMap K L (f.derivative.eval a₀) := by
    rw [hg, derivative_map, eval_map, eval₂_hom]
  obtain ⟨a, ha, hsub⟩ := hL g (hmon.map _) hgint (algebraMap K L a₀) ha₀
    (by rwa [hgev]) (by rwa [hgdev])
  have hav : w a ≤ 1 := by
    rw [show a = (a - algebraMap K L a₀) + algebraMap K L a₀ by ring]
    exact w.map_add_le hsub.le ha₀
  have hda : w (g.derivative.eval a) = 1 := by
    have h2 : w (g.derivative.eval a - algebraMap K L (f.derivative.eval a₀)) < 1 := by
      rw [← hgdev]
      exact (val_eval_sub_le hgint.derivative hav ha₀).trans_lt hsub
    rw [show g.derivative.eval a = g.derivative.eval (algebraMap K L a₀) +
      (g.derivative.eval a - g.derivative.eval (algebraMap K L a₀)) by ring,
      Valuation.map_add_eq_of_lt_left] <;> rw [hgdev, hder]
    exact h2
  have hfixa : ∀ σ : L ≃ₐ[K] L, σ a = a := by
    intro σ
    have hroot : g.eval (σ a) = 0 := by
      rw [hg, eval_map_algebraMap, aeval_algHom_apply, ← eval_map_algebraMap, ← hg, ha,
        map_zero]
    have hclose : w (σ a - a) < 1 := by
      have : σ a - a = σ (a - algebraMap K L a₀) - (a - algebraMap K L a₀) := by
        rw [map_sub, AlgEquiv.commutes]
        ring
      rw [this]
      exact (w.map_sub _ _).trans_lt (max_lt (by rw [hinv]; exact hsub) hsub)
    exact eq_of_eval_eq_zero hgint hav ha hroot hclose hda
  obtain ⟨c, rfl⟩ := hfix a hfixa
  refine ⟨c, ?_, ?_⟩
  · apply (algebraMap K L).injective
    rw [← hgev, ha, map_zero]
  · rw [Valuation.comap_apply, map_sub]
    exact hsub

/-- Root finding modulo the maximal ideal ascends from `K` to `B` when every integral element
of `L ⊇ B` is congruent to an integral element of `K`. -/
theorem valResidueRoot_comap {B L : Type*} [Field B] [Field L] [Algebra K B] [Algebra K L]
    [Algebra B L] [IsScalarTower K B L] {w : Valuation L ℝ≥0}
    (hK : ValResidueRoot (w.comap (algebraMap K L)))
    (hres : ∀ x : L, w x ≤ 1 → ∃ c : K, w (algebraMap K L c) ≤ 1 ∧
      w (x - algebraMap K L c) < 1) :
    ValResidueRoot (w.comap (algebraMap B L)) := by
  classical
  intro f hint ⟨i0, hi0, hu⟩
  simp only [Valuation.comap_apply] at hint hu
  choose c hc1 hc2 using fun i => hres (algebraMap B L (f.coeff i)) (hint i)
  set N := f.natDegree
  set g : K[X] := ∑ i ∈ range (N + 1), Polynomial.C (c i) * X ^ i with hg
  have hgint : IntPoly (w.comap (algebraMap K L)) g :=
    IntPoly.sum _ fun i _ => IntPoly.C_mul_X_pow (by rw [Valuation.comap_apply]; exact hc1 i) _
  have hi0N : i0 ∈ range (N + 1) := by
    refine mem_range.mpr (Nat.lt_succ_of_le (le_natDegree_of_ne_zero fun h0 => ?_))
    rw [h0, map_zero, map_zero] at hu
    exact zero_ne_one hu
  have hgc : g.coeff i0 = c i0 := by
    rw [hg, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [sum_ite_eq, ite_eq_left_of_eq_true _ _ (eq_true hi0N)]
  have hcu : w (algebraMap K L (c i0)) = 1 := by
    rw [show algebraMap K L (c i0) = algebraMap B L (f.coeff i0) +
      -(algebraMap B L (f.coeff i0) - algebraMap K L (c i0)) by ring,
      Valuation.map_add_eq_of_lt_left] <;> rw [hu]
    rw [Valuation.map_neg]
    exact hc2 i0
  obtain ⟨b, hb1, hb2⟩ := hK g hgint ⟨i0, hi0, by rw [hgc, Valuation.comap_apply, hcu]⟩
  rw [Valuation.comap_apply] at hb1 hb2
  refine ⟨algebraMap K B b, ?_, ?_⟩
  · rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]
    exact hb1
  have hgev : algebraMap K L (g.eval b) =
      ∑ i ∈ range (N + 1), algebraMap K L (c i) * algebraMap K L b ^ i := by
    simp [hg, eval_finsetSum]
  have hfev : algebraMap B L (f.eval (algebraMap K B b)) =
      ∑ i ∈ range (N + 1), algebraMap B L (f.coeff i) * algebraMap K L b ^ i := by
    rw [eval_eq_sum_range, map_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
  rw [Valuation.comap_apply, hfev]
  have hdiff : ∑ i ∈ range (N + 1), algebraMap B L (f.coeff i) * algebraMap K L b ^ i =
      algebraMap K L (g.eval b) + ∑ i ∈ range (N + 1),
        (algebraMap B L (f.coeff i) - algebraMap K L (c i)) * algebraMap K L b ^ i := by
    rw [hgev, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hdiff]
  refine (w.map_add _ _).trans_lt (max_lt hb2 (w.map_sum_lt one_ne_zero fun i _ => ?_))
  rw [map_mul, map_pow]
  exact (mul_le_of_le_one_right zero_le (pow_le_one' hb1 _)).trans_lt (hc2 i)

/-- Discrete values on integral elements give a uniformizer. -/
theorem exists_valUniformizer {D : ℕ} (hD : 0 < D) {q : ℝ≥0} (hq0 : 0 < q) (hq1 : q < 1)
    (hdisc : ∀ x : K, x ≠ 0 → v x ≤ 1 → ∃ k : ℕ, v x ^ D = q ^ k) {c : K} (hc0 : 0 < v c)
    (hc1 : v c < 1) : ∃ π : K, ValUniformizer v π := by
  classical
  have hD0 : D ≠ 0 := hD.ne'
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ b : K, b ≠ 0 ∧ v b ≤ 1 ∧ v b ^ D = q ^ n := by
    have hc0' : c ≠ 0 := fun h0 => by rw [h0, map_zero] at hc0; exact lt_irrefl _ hc0
    obtain ⟨k, hk⟩ := hdisc c hc0' hc1.le
    refine ⟨k, Nat.pos_of_ne_zero fun h0 => ?_, c, hc0', hc1.le, hk⟩
    rw [h0, pow_zero] at hk
    exact absurd hk (pow_lt_one₀ zero_le hc1 hD0).ne
  obtain ⟨hn0, π, hπ0, hπ1, hπ⟩ := Nat.find_spec hex
  set n0 := Nat.find hex
  have hvπ0 : 0 < v π := by
    rw [pos_iff_ne_zero, Ne, Valuation.zero_iff]
    exact hπ0
  have hvπ1 : v π < 1 := by
    have : v π ^ D < 1 := by rw [hπ]; exact pow_lt_one₀ zero_le hq1 hn0.ne'
    exact (pow_lt_one_iff_of_nonneg zero_le hD0).mp this
  refine ⟨π, hvπ0, hvπ1, fun b hb0 hb1 => ?_⟩
  obtain ⟨k, hk⟩ := hdisc b hb0 hb1
  set j := k / n0
  set r := k % n0
  have hkjr : k = n0 * j + r := (Nat.div_add_mod k n0).symm
  have hπj0 : π ^ j ≠ 0 := pow_ne_zero _ hπ0
  have hb' : v (b / π ^ j) ^ D = q ^ r := by
    have hqj : q ^ (n0 * j) ≠ 0 := pow_ne_zero _ hq0.ne'
    rw [map_div₀, div_pow, map_pow, ← pow_mul, mul_comm j D, pow_mul, hπ, hk, ← pow_mul,
      hkjr, pow_add, mul_div_cancel_left₀ _ hqj]
  have hr0 : r = 0 := by
    by_contra hr
    have hrlt : r < n0 := Nat.mod_lt _ hn0
    refine Nat.find_min hex hrlt ⟨Nat.pos_of_ne_zero hr, b / π ^ j,
      div_ne_zero hb0 hπj0, ?_, hb'⟩
    have : v (b / π ^ j) ^ D ≤ 1 := by rw [hb']; exact pow_le_one₀ zero_le hq1.le
    exact (pow_le_one_iff_of_nonneg zero_le hD0).mp this
  refine ⟨j, (pow_left_inj₀ zero_le zero_le hD0).mp ?_⟩
  rw [hk, ← pow_mul, mul_comm j D, pow_mul, hπ, ← pow_mul, hkjr, hr0, add_zero]

end Field

section Tower

variable {B C M : Type*} [Field B] [Field C] [Field M] [Algebra B C] [Algebra C M] [Algebra B M]
  [IsScalarTower B C M]

/-- The hypotheses of the cyclic step for `C / B`, read off from hypotheses on `M`. -/
theorem cyclicHyp_of_tower [Normal B M] {w : Valuation M ℝ≥0} {π : B}
    (hinv : ∀ (σ : M ≃ₐ[B] M) (x : M), w (σ x) = w x) (hp : (finrank B C).Prime)
    (hH : ValHensel (w.comap (algebraMap B M)))
    (hR : ValResidueRoot (w.comap (algebraMap B M)))
    (hU : ValUniformizer (w.comap (algebraMap B M)) π)
    (hres : ∀ x : M, w x ≤ 1 → ∃ c : B, w (algebraMap B M c) ≤ 1 ∧
      w (x - algebraMap B M c) < 1) :
    CyclicHyp (w.comap (algebraMap C M)) π := by
  have hcomp : (w.comap (algebraMap C M)).comap (algebraMap B C) = w.comap (algebraMap B M) := by
    rw [← Valuation.comap_comp, ← IsScalarTower.algebraMap_eq]
  refine ⟨fun σ x => ?_, hp, hcomp ▸ hH, hcomp ▸ hR, hcomp ▸ hU, fun x hx => ?_⟩
  · simp only [Valuation.comap_apply]
    rw [← AlgEquiv.liftNormal_commutes σ M x, hinv]
  · simp only [Valuation.comap_apply] at hx ⊢
    obtain ⟨c, hc1, hc2⟩ := hres _ hx
    refine ⟨c, ?_, ?_⟩
    · rwa [← IsScalarTower.algebraMap_apply]
    · rwa [map_sub, ← IsScalarTower.algebraMap_apply]

end Tower

variable {E M : Type*} [Field E] [Field M] [Algebra E M] [FiniteDimensional E M] [IsGalois E M]

/-- The hypotheses of the reduction to the cyclic step. -/
structure ReductionHyp (w : Valuation M ℝ≥0) (p : ℕ) : Prop where
  inv : ∀ (σ : Gal(M/E)) (x : M), w (σ x) = w x
  prime : p.Prime
  natCast : ∀ m : ℕ, ¬ p ∣ m → w (m : M) = 1
  hensel : ValHensel w
  residueRoot : ValResidueRoot (w.comap (algebraMap E M))
  res : ∀ x : M, w x ≤ 1 → ∃ c : E, w (algebraMap E M c) ≤ 1 ∧ w (x - algebraMap E M c) < 1
  disc : ∃ D : ℕ, 0 < D ∧ ∃ q : ℝ≥0, 0 < q ∧ q < 1 ∧
    ∀ x : M, x ≠ 0 → w x ≤ 1 → ∃ k : ℕ, w x ^ D = q ^ k
  small : ∃ c : E, 0 < w (algebraMap E M c) ∧ w (algebraMap E M c) < 1

namespace ReductionHyp

variable {w : Valuation M ℝ≥0} {p : ℕ} (h : ReductionHyp (E := E) w p)

include h

omit [FiniteDimensional E M] [IsGalois E M] in
theorem inv_of (B : IntermediateField E M) (σ : M ≃ₐ[B] M) (x : M) : w (σ x) = w x :=
  h.inv (σ.restrictScalars E) x

theorem hensel_of (B : IntermediateField E M) : ValHensel (w.comap (algebraMap B M)) :=
  valHensel_comap h.hensel (h.inv_of B) fun x hx =>
    (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hx

theorem henselE : ValHensel (w.comap (algebraMap E M)) :=
  valHensel_comap h.hensel h.inv fun x hx => (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hx

omit [FiniteDimensional E M] [IsGalois E M] in
theorem res_of (B : IntermediateField E M) (x : M) (hx : w x ≤ 1) :
    ∃ c : B, w (algebraMap B M c) ≤ 1 ∧ w (x - algebraMap B M c) < 1 := by
  obtain ⟨c, hc1, hc2⟩ := h.res x hx
  refine ⟨algebraMap E B c, ?_, ?_⟩ <;> rwa [← IsScalarTower.algebraMap_apply]

omit [FiniteDimensional E M] [IsGalois E M] in
theorem residueRoot_of (B : IntermediateField E M) :
    ValResidueRoot (w.comap (algebraMap B M)) :=
  valResidueRoot_comap h.residueRoot h.res

omit [FiniteDimensional E M] [IsGalois E M] in
theorem unif_of (B : IntermediateField E M) :
    ∃ π : B, ValUniformizer (w.comap (algebraMap B M)) π := by
  obtain ⟨D, hD, q, hq0, hq1, hdisc⟩ := h.disc
  obtain ⟨c, hc0, hc1⟩ := h.small
  refine exists_valUniformizer hD hq0 hq1 (fun x hx0 hx1 => hdisc _ ?_ hx1)
    (c := algebraMap E B c) ?_ ?_
  · exact (map_ne_zero_iff _ (algebraMap B M).injective).mpr hx0
  · rwa [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]
  · rwa [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]

/-- The cyclic step for a Galois subextension `C / B` of prime degree. -/
theorem cyclic (B : IntermediateField E M) (C : IntermediateField B M) [IsGalois B C]
    (hp : (finrank B C).Prime) (u : B) (hu : w (algebraMap B M u) = 1) :
    ∃ x : C, w (algebraMap C M x) = 1 ∧ Algebra.norm B x = u := by
  obtain ⟨π, hπ⟩ := h.unif_of B
  have hc : CyclicHyp (w.comap (algebraMap C M)) π :=
    cyclicHyp_of_tower (h.inv_of B) hp (h.hensel_of B) (h.residueRoot_of B) hπ (h.res_of B)
  obtain ⟨x, hx, hxN⟩ := hc.exists_norm_eq u (by
    rwa [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply])
  exact ⟨x, hx, hxN⟩

/-- The `p`-group case: if `[M : B]` is a power of `p`, every unit of `B` is a norm from `M`. -/
theorem pgroup (k : ℕ) : ∀ B : IntermediateField E M, finrank B M = p ^ k →
    ∀ u : B, w (algebraMap B M u) = 1 → ∃ z : M, w z = 1 ∧ Algebra.norm B z = u := by
  have : Fact p.Prime := ⟨h.prime⟩
  induction k with
  | zero =>
    intro B hB u hu
    refine ⟨algebraMap B M u, hu, ?_⟩
    rw [Algebra.norm_algebraMap, hB, pow_zero, pow_one]
  | succ k ih =>
    intro B hB u hu
    have hcard : Nat.card Gal(M/B) = p ^ (k + 1) := by
      rw [IsGalois.card_aut_eq_finrank, hB]
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime p (n := k)
      (by rw [hcard]; exact pow_dvd_pow p (Nat.le_succ k))
    have hidx : H.index = p := by
      have := H.card_mul_index
      rw [hH, hcard, pow_succ] at this
      exact Nat.eq_of_mul_eq_mul_left (pow_pos h.prime.pos k) this
    have hnormal : H.Normal := Subgroup.normal_of_index_eq_minFac_card (by
      rw [hidx, hcard, Nat.pow_minFac (by omega), h.prime.minFac_eq])
    set C := IntermediateField.fixedField H
    have hCM : finrank C M = p ^ k := by
      rw [IntermediateField.finrank_fixedField_eq_card, hH]
    have hBC : finrank B C = p := by
      have := Module.finrank_mul_finrank B C M
      rw [hCM, hB, pow_succ, mul_comm] at this
      exact Nat.eq_of_mul_eq_mul_left (pow_pos h.prime.pos k) this
    obtain ⟨x, hx, hxN⟩ := h.cyclic B C (hBC ▸ h.prime) u hu
    set C' : IntermediateField E M := C.restrictScalars E
    obtain ⟨z, hz, hzN⟩ := ih C' hCM ⟨x, x.2⟩ hx
    refine ⟨z, hz, ?_⟩
    have hzC : Algebra.norm C z = x := by
      let e : C' ≃+* C :=
        { toFun := fun y => ⟨y.1, y.2⟩
          invFun := fun y => ⟨y.1, y.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl
          map_add' := fun _ _ => rfl }
      rw [← Algebra.norm_eq_of_ringEquiv e (by ext; rfl), hzN]
      rfl
    rw [← Algebra.norm_norm (S := C), hzC, hxN]

/-- Prime-to-`p` roots of units of `E`. -/
theorem exists_pow_eq {m : ℕ} (hm : ¬ p ∣ m) (u : E) (hu : w (algebraMap E M u) = 1) :
    ∃ y : E, w (algebraMap E M y) = 1 ∧ y ^ m = u := by
  classical
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  set f : E[X] := X ^ m - Polynomial.C u with hf
  have hfint : IntPoly (w.comap (algebraMap E M)) f := by
    intro i
    rw [hf, coeff_sub, coeff_X_pow, coeff_C]
    split_ifs <;> first | omega | simp [Valuation.comap_apply, hu]
  obtain ⟨b, hb1, hb2⟩ := h.residueRoot f hfint ⟨m, Nat.pos_of_ne_zero hm0, by
    rw [hf, coeff_sub, coeff_X_pow, coeff_C, ite_eq_left_of_eq_true _ _ (eq_true rfl),
      ite_eq_right_of_eq_false _ _ (eq_false hm0), sub_zero, Valuation.comap_apply, map_one,
      map_one]⟩
  rw [Valuation.comap_apply] at hb1 hb2
  have hfb : f.eval b = b ^ m - u := by simp [hf]
  rw [hfb] at hb2
  have hbm : w (algebraMap E M (b ^ m)) = 1 := by
    rw [show b ^ m = u + (b ^ m - u) by ring, map_add, Valuation.map_add_eq_of_lt_left, hu]
    rwa [hu]
  have hb : w (algebraMap E M b) = 1 := by
    rw [map_pow, map_pow] at hbm
    exact (pow_left_inj₀ zero_le zero_le hm0).mp (by rw [hbm, one_pow])
  have hder : f.derivative.eval b = (m : E) * b ^ (m - 1) := by
    simp [hf, derivative_X_pow]
  obtain ⟨y, hy, hyb⟩ := h.henselE f (monic_X_pow_sub_C u hm0) hfint b
    (by rw [Valuation.comap_apply]; exact hb1) (by rwa [Valuation.comap_apply, hfb])
    (by rw [Valuation.comap_apply, hder, map_mul, map_mul, map_pow, map_pow, hb, one_pow,
      mul_one, map_natCast, h.natCast m hm])
  rw [Valuation.comap_apply] at hyb
  refine ⟨y, ?_, ?_⟩
  · rw [show y = b + (y - b) by ring, map_add, Valuation.map_add_eq_of_lt_left, hb]
    rwa [hb]
  · have : f.eval y = y ^ m - u := by simp [hf]
    rw [hy] at this
    exact (sub_eq_zero.mp this.symm)

/-- **Reduction.** Every unit of `E` is the norm of a unit of `M`. -/
theorem exists_norm_eq (u : E) (hu : w (algebraMap E M u) = 1) :
    ∃ z : M, w z = 1 ∧ Algebra.norm E z = u := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨a, m, hm, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (finrank_pos (R := E) (M := M)).ne'
    p h.prime.ne_one
  have hcard : Nat.card Gal(M/E) = finrank E M := IsGalois.card_aut_eq_finrank E M
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime p (n := a)
    (by rw [hcard, hN]; exact dvd_mul_right _ _)
  set B := IntermediateField.fixedField H
  have hBM : finrank B M = p ^ a := by
    rw [IntermediateField.finrank_fixedField_eq_card, hH]
  have hEB : finrank E B = m := by
    have := Module.finrank_mul_finrank E B M
    rw [hBM, hN, mul_comm] at this
    exact Nat.eq_of_mul_eq_mul_left (pow_pos h.prime.pos a) this
  obtain ⟨y, hy, hym⟩ := h.exists_pow_eq hm u hu
  obtain ⟨z, hz, hzN⟩ := h.pgroup a B hBM (algebraMap E B y)
    (by rw [← IsScalarTower.algebraMap_apply]; exact hy)
  refine ⟨z, hz, ?_⟩
  rw [← Algebra.norm_norm (S := B), hzN, Algebra.norm_algebraMap, hEB, hym]

end ReductionHyp

end Langlands.ClassFieldTheory.Local.SeparableInertiaNorm
