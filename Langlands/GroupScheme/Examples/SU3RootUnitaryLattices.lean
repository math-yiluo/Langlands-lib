import Langlands.GroupScheme.Examples.SU3RootUnitaryCoordinates
import Langlands.GroupScheme.Examples.SU3RootParametersLocalValuation

/-! # Valuation lattices for the ramified quadratic unitary integral models

Let `L / K` be a separable quadratic extension with conjugation `σ`, and let `ω` be a
conjugation-invariant additive valuation on `L` whose values on `K^×` are integers and which
takes the value `1/2` (the ramified case). This module proves the arithmetic of
Kaletha–Prasad §2.8 and Appendix C.4 needed for the integral models `X_{r,s}`:

* the number `μ = sup {ω(x) | x + σ(x) = 1}` of (2.8.1) is a maximum, giving a trace-one
  element `λ` with `ω(λ) = μ`;
* Lemma 2.8.1(2): every nonzero trace-zero element `y` has `ω(y) ∈ ℤ + 1/2 + μ`;
* Lemma 3.2.2: if `v + σ(v) = u σ(u)` and `ω(v) ≥ 2r + μ` then `ω(u) ≥ r`;
* explicit bases of the lattices `Y_r = {u | ω(u) ≥ r}` and `Z_s = {z | z + σ(z) = 0,
  ω(z) ≥ s + μ}`;
* the bilinear correction `σ(λ) x σ(y) − λ σ(x) y` of (C.4.2) lies in `Z_s` for `x, y ∈ Y_r`,
  when `2r ∈ ℤ` and `s ≤ 2r + 1/2`.
-/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.SU3Root

/-- Moving a real constant across an inequality in `WithTop ℝ`. -/
theorem coe_le_add_coe_iff (r c : ℝ) (x : WithTop ℝ) :
    (r : WithTop ℝ) ≤ x + (c : WithTop ℝ) ↔ ((r - c : ℝ) : WithTop ℝ) ≤ x := by
  induction x with
  | top => simp
  | coe t =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

/-- The ceiling is the least integer shift reaching a real number. -/
theorem le_int_add_ceil_iff (t : ℝ) (n : ℤ) : t ≤ n + ⌈t⌉ ↔ 0 ≤ n := by
  constructor
  · intro h
    by_contra hn
    have h1 : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    have h2 := Int.ceil_lt_add_one t
    linarith
  · intro hn
    have h1 : (0 : ℝ) ≤ n := by exact_mod_cast hn
    have h2 := Int.le_ceil t
    linarith

/-- An integer is never a half-odd integer. -/
theorem int_ne_int_add_half (n m : ℤ) : (n : ℝ) ≠ m + 1 / 2 := by
  intro h
  have h' : ((2 * (n - m) : ℤ) : ℝ) = 1 := by push_cast; linarith
  have h'' : 2 * (n - m) = 1 := by exact_mod_cast h'
  omega

section Lattices

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

local notation "σ" => conjugation K L

local instance su3RootUnitaryLatticesFiniteDimensional : FiniteDimensional K L :=
  .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two K L]; decide)

/-- The hypotheses on the valuation of a ramified separable quadratic extension: `ω` is
invariant under the conjugation, its values on `K^×` are integers, and it takes the value
`1/2` (so `L / K` has ramification index two). -/
structure IsRamifiedQuadraticValuation (ω : AddValuation L (WithTop ℝ)) : Prop where
  conjugation_eq : ∀ z : L, ω (σ z) = ω z
  base_int : ∀ a : K, a ≠ 0 → ∃ n : ℤ, ω (algebraMap K L a) = ((n : ℝ) : WithTop ℝ)
  exists_half : ∃ π : L, ω π = ((1 / 2 : ℝ) : WithTop ℝ)

/-- The number `μ = sup {ω(x) | x ∈ L, x + σ(x) = 1}` of Kaletha–Prasad (2.8.1). -/
def mu (ω : AddValuation L (WithTop ℝ)) : ℝ :=
  sSup {t : ℝ | ∃ x : L, x + σ x = 1 ∧ ω x = (t : WithTop ℝ)}

/-- A chosen nonzero trace-zero element `f₀ ∈ L`. -/
def traceZeroElement : L := Classical.choose (exists_ne_zero_add_conjugation_eq_zero K L)

theorem traceZeroElement_ne_zero : traceZeroElement K L ≠ 0 :=
  (Classical.choose_spec (exists_ne_zero_add_conjugation_eq_zero K L)).1

theorem traceZeroElement_add : traceZeroElement K L + σ (traceZeroElement K L) = 0 :=
  (Classical.choose_spec (exists_ne_zero_add_conjugation_eq_zero K L)).2

variable {K L}

/-- Nonzero elements have real values. -/
theorem exists_omega_eq_coe (ω : AddValuation L (WithTop ℝ)) {x : L} (hx : x ≠ 0) :
    ∃ t : ℝ, ω x = (t : WithTop ℝ) := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (ω.ne_top_iff.mpr hx)
  exact ⟨t, ht.symm⟩

/-- Values of integer powers. -/
theorem omega_zpow (ω : AddValuation L (WithTop ℝ)) {x : L} (hx : x ≠ 0) (t : ℝ)
    (ht : ω x = (t : WithTop ℝ)) (n : ℤ) : ω (x ^ n) = ((n * t : ℝ) : WithTop ℝ) := by
  have hinv : ω x⁻¹ = ((-t : ℝ) : WithTop ℝ) := by
    obtain ⟨s, hs⟩ := exists_omega_eq_coe ω (inv_ne_zero hx)
    have h1 : ω (x * x⁻¹) = 0 := by rw [mul_inv_cancel₀ hx, ω.map_one]
    rw [ω.map_mul, ht, hs, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at h1
    rw [hs, WithTop.coe_eq_coe]
    linarith
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one₀ hx, ω.map_mul, ih, ht, ← WithTop.coe_add, WithTop.coe_eq_coe]
    push_cast
    ring
  | pred n ih =>
    rw [zpow_sub_one₀ hx, ω.map_mul, ih, hinv, ← WithTop.coe_add, WithTop.coe_eq_coe]
    push_cast
    ring

namespace IsRamifiedQuadraticValuation

variable {ω : AddValuation L (WithTop ℝ)} (hω : IsRamifiedQuadraticValuation K L ω)
include hω

theorem bar_eq (z : L) : ω ((fieldInvolution K L).bar z) = ω z := hω.conjugation_eq z

/-- Values on `K` are never half-odd integers. -/
theorem omega_algebraMap_ne_half (a : K) (m : ℤ) :
    ω (algebraMap K L a) ≠ (((m : ℝ) + 1 / 2 : ℝ) : WithTop ℝ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, ω.map_zero]
    exact WithTop.top_ne_coe
  · obtain ⟨n, hn⟩ := hω.base_int a ha
    rw [hn, Ne, WithTop.coe_eq_coe]
    exact int_ne_int_add_half n m

/-- The chosen element of value `1/2`. -/
def uniformizer : L := hω.exists_half.choose

theorem omega_uniformizer : ω hω.uniformizer = ((1 / 2 : ℝ) : WithTop ℝ) :=
  hω.exists_half.choose_spec

theorem uniformizer_ne_zero : hω.uniformizer ≠ 0 := by
  intro h
  have h' := hω.omega_uniformizer
  rw [h, ω.map_zero] at h'
  exact WithTop.top_ne_coe h'

theorem uniformizer_ne_algebraMap (a : K) : hω.uniformizer ≠ algebraMap K L a := by
  intro h
  have h' := hω.omega_uniformizer
  rw [h] at h'
  exact hω.omega_algebraMap_ne_half a 0 (by rw [h']; norm_num)

/-- `1` and the uniformizer are linearly independent over `K`. -/
theorem linearIndependent_one_uniformizer : LinearIndependent K ![1, hω.uniformizer] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
  by_cases ht : t = 0
  · subst ht
    rw [map_zero, zero_mul, add_zero] at h
    exact ⟨(map_eq_zero_iff _ (algebraMap K L).injective).mp h, rfl⟩
  · exfalso
    have ht' : algebraMap K L t ≠ 0 := (map_ne_zero _).mpr ht
    apply hω.uniformizer_ne_algebraMap (-s / t)
    rw [map_div₀, map_neg, eq_div_iff ht']
    linear_combination h

/-- The basis `(1, π)` of `L` over `K`. -/
def uniformizerBasis : Module.Basis (Fin 2) K L :=
  basisOfLinearIndependentOfCardEqFinrank hω.linearIndependent_one_uniformizer
    (by rw [Algebra.IsQuadraticExtension.finrank_eq_two K L, Fintype.card_fin])

@[simp] theorem uniformizerBasis_zero : hω.uniformizerBasis 0 = 1 := by
  simp [uniformizerBasis]

@[simp] theorem uniformizerBasis_one : hω.uniformizerBasis 1 = hω.uniformizer := by
  simp [uniformizerBasis]

/-- Every element of `L` is `c₀ + c₁ π` with `c₀, c₁ ∈ K`. -/
theorem exists_decomposition (x : L) :
    ∃ c₀ c₁ : K, algebraMap K L c₀ + algebraMap K L c₁ * hω.uniformizer = x := by
  refine ⟨hω.uniformizerBasis.repr x 0, hω.uniformizerBasis.repr x 1, ?_⟩
  conv_rhs => rw [← hω.uniformizerBasis.sum_repr x]
  rw [Fin.sum_univ_two, uniformizerBasis_zero, uniformizerBasis_one, Algebra.smul_def,
    Algebra.smul_def, mul_one]

theorem omega_algebraMap_ne_omega_mul (c₀ c₁ : K) (h : c₀ ≠ 0 ∨ c₁ ≠ 0) :
    ω (algebraMap K L c₀) ≠ ω (algebraMap K L c₁ * hω.uniformizer) := by
  rw [ω.map_mul, hω.omega_uniformizer]
  rcases eq_or_ne c₁ 0 with rfl | h₁
  · have h₀ : c₀ ≠ 0 := h.resolve_right (not_not.mpr rfl)
    rw [map_zero, ω.map_zero, WithTop.top_add]
    exact ω.ne_top_iff.mpr ((map_ne_zero _).mpr h₀)
  · obtain ⟨m, hm⟩ := hω.base_int c₁ h₁
    rw [hm, ← WithTop.coe_add]
    exact hω.omega_algebraMap_ne_half c₀ m

/-- The value of `c₀ + c₁ π` is `min (ω c₀) (ω c₁ + 1/2)`. -/
theorem omega_add_mul_uniformizer (c₀ c₁ : K) :
    ω (algebraMap K L c₀ + algebraMap K L c₁ * hω.uniformizer) =
      min (ω (algebraMap K L c₀)) (ω (algebraMap K L c₁) + ((1 / 2 : ℝ) : WithTop ℝ)) := by
  by_cases h : c₀ = 0 ∧ c₁ = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [ω.map_add_of_distinct_val (hω.omega_algebraMap_ne_omega_mul c₀ c₁ (by tauto)),
      ω.map_mul, hω.omega_uniformizer]

/-- An element of `K` of value one, namely `π σ(π)`. -/
theorem exists_baseUniformizer : ∃ ϖ : K, ω (algebraMap K L ϖ) = ((1 : ℝ) : WithTop ℝ) := by
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_conjugation_eq K L
    (x := hω.uniformizer * σ hω.uniformizer)
    (by rw [map_mul, conjugation_involutive K L hω.uniformizer, mul_comm])
  refine ⟨c, ?_⟩
  rw [hc, ω.map_mul, hω.conjugation_eq, hω.omega_uniformizer, ← WithTop.coe_add,
    WithTop.coe_eq_coe]
  norm_num

/-- The chosen base uniformizer `ϖ ∈ K`, of value one. -/
def baseUniformizer : K := hω.exists_baseUniformizer.choose

theorem omega_baseUniformizer :
    ω (algebraMap K L hω.baseUniformizer) = ((1 : ℝ) : WithTop ℝ) :=
  hω.exists_baseUniformizer.choose_spec

theorem baseUniformizer_ne_zero : hω.baseUniformizer ≠ 0 := by
  intro h
  have h' := hω.omega_baseUniformizer
  rw [h, map_zero, ω.map_zero] at h'
  exact WithTop.top_ne_coe h'

theorem omega_baseUniformizer_zpow (n : ℤ) :
    ω (algebraMap K L (hω.baseUniformizer ^ n)) = ((n : ℝ) : WithTop ℝ) := by
  rw [map_zpow₀, omega_zpow ω ((map_ne_zero _).mpr hω.baseUniformizer_ne_zero) 1
    hω.omega_baseUniformizer, mul_one]

/-- Values of nonzero elements are half-integers: `2 ω(x) = ω(x σ(x)) ∈ ℤ`. -/
theorem exists_half_integer {x : L} (hx : x ≠ 0) :
    ∃ n : ℤ, ω x = (((n : ℝ) / 2 : ℝ) : WithTop ℝ) := by
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_conjugation_eq K L (x := x * σ x)
    (by rw [map_mul, conjugation_involutive K L x, mul_comm])
  have hσx : σ x ≠ 0 := by
    intro h
    exact hx ((map_eq_zero_iff _ (conjugation K L).injective).mp h)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact mul_ne_zero hx hσx hc.symm
  obtain ⟨n, hn⟩ := hω.base_int c hc0
  obtain ⟨t, ht⟩ := exists_omega_eq_coe ω hx
  refine ⟨n, ?_⟩
  have h2 : ω (x * σ x) = ((t + t : ℝ) : WithTop ℝ) := by
    rw [ω.map_mul, hω.conjugation_eq, ht, WithTop.coe_add]
  rw [← hc, hn, WithTop.coe_eq_coe] at h2
  rw [ht, WithTop.coe_eq_coe]
  linarith

/-! ### The number `μ` and a trace-one element of maximal value -/

/-- Trace-one elements have nonpositive value. -/
theorem omega_le_zero_of_add_eq_one {x : L} (hx : x + σ x = 1) :
    ω x ≤ ((0 : ℝ) : WithTop ℝ) := by
  have h := ω.map_add x (σ x)
  rw [hω.conjugation_eq, min_self, hx, ω.map_one] at h
  exact h

omit hω in
theorem ne_zero_of_add_eq_one {x : L} (hx : x + σ x = 1) : x ≠ 0 := by
  rintro rfl
  simp at hx

/-- The supremum (2.8.1) is a maximum, attained by a trace-one element. -/
theorem isGreatest_mu :
    IsGreatest {t : ℝ | ∃ x : L, x + σ x = 1 ∧ ω x = (t : WithTop ℝ)} (mu K L ω) := by
  set S := {t : ℝ | ∃ x : L, x + σ x = 1 ∧ ω x = (t : WithTop ℝ)}
  set P : ℤ → Prop := fun n => ∃ x : L, x + σ x = 1 ∧ ω x = (((n : ℝ) / 2 : ℝ) : WithTop ℝ)
  have hbdd : ∃ b : ℤ, ∀ n, P n → n ≤ b := by
    refine ⟨0, fun n ⟨x, hx, hxn⟩ => ?_⟩
    have h := hω.omega_le_zero_of_add_eq_one hx
    rw [hxn, WithTop.coe_le_coe] at h
    have h' : (n : ℝ) ≤ 0 := by linarith
    exact_mod_cast h'
  have hne : ∃ n, P n := by
    obtain ⟨n, hn⟩ := hω.exists_half_integer
      (ne_zero_of_add_eq_one (traceOne_add_conjugate K L))
    exact ⟨n, traceOne K L, traceOne_add_conjugate K L, hn⟩
  obtain ⟨N, ⟨xN, hxN, hxNv⟩, hN⟩ := Int.exists_greatest_of_bdd hbdd hne
  have hgr : IsGreatest S ((N : ℝ) / 2) := by
    refine ⟨⟨xN, hxN, hxNv⟩, ?_⟩
    rintro t ⟨x, hx, hxt⟩
    obtain ⟨n, hn⟩ := hω.exists_half_integer (ne_zero_of_add_eq_one hx)
    have hnN := hN n ⟨x, hx, hn⟩
    rw [hn, WithTop.coe_eq_coe] at hxt
    have : (n : ℝ) ≤ N := by exact_mod_cast hnN
    linarith
  have hmu : mu K L ω = (N : ℝ) / 2 := hgr.csSup_eq
  rw [hmu]
  exact hgr

/-- Every trace-one element has value at most `μ`. -/
theorem omega_le_mu {x : L} (hx : x + σ x = 1) : ω x ≤ ((mu K L ω : ℝ) : WithTop ℝ) := by
  obtain ⟨t, ht⟩ := exists_omega_eq_coe ω (ne_zero_of_add_eq_one hx)
  rw [ht, WithTop.coe_le_coe]
  exact hω.isGreatest_mu.2 ⟨x, hx, ht⟩

theorem exists_traceOne_omega_eq_mu :
    ∃ x : L, x + σ x = 1 ∧ ω x = ((mu K L ω : ℝ) : WithTop ℝ) :=
  hω.isGreatest_mu.1

theorem mu_le_zero : mu K L ω ≤ 0 := by
  obtain ⟨x, hx, hxv⟩ := hω.exists_traceOne_omega_eq_mu
  have h := hω.omega_le_zero_of_add_eq_one hx
  rwa [hxv, WithTop.coe_le_coe] at h

/-- A trace-one element `λ ∈ L_{tr=1,max}` of maximal value `μ`, as in (2.8.2). -/
def traceOneMax : L := hω.exists_traceOne_omega_eq_mu.choose

theorem traceOneMax_add : hω.traceOneMax + σ hω.traceOneMax = 1 :=
  hω.exists_traceOne_omega_eq_mu.choose_spec.1

theorem omega_traceOneMax : ω hω.traceOneMax = ((mu K L ω : ℝ) : WithTop ℝ) :=
  hω.exists_traceOne_omega_eq_mu.choose_spec.2

theorem traceOneMax_ne_zero : hω.traceOneMax ≠ 0 :=
  ne_zero_of_add_eq_one hω.traceOneMax_add

/-! ### Lemma 2.8.1(2) and Lemma 3.2.2 -/

/-- Kaletha–Prasad Lemma 2.8.1(2), ramified case: a nonzero trace-zero element `y` has
`ω(y) ∈ ℤ + 1/2 + μ`. -/
theorem traceZero_parity {y : L} (hy : y ≠ 0) (hy' : y + σ y = 0) :
    ∃ m : ℤ, ω y = (((m : ℝ) + 1 / 2 + mu K L ω : ℝ) : WithTop ℝ) := by
  have hlam0 := hω.traceOneMax_ne_zero
  obtain ⟨c₀, c₁, hc⟩ := hω.exists_decomposition (y / hω.traceOneMax)
  have hyt : y = hω.traceOneMax *
      (algebraMap K L c₀ + algebraMap K L c₁ * hω.uniformizer) := by
    rw [hc, mul_div_cancel₀ _ hlam0]
  have hσy : σ y = -y := by linear_combination hy'
  rcases le_or_gt (ω (algebraMap K L c₁) + ((1 / 2 : ℝ) : WithTop ℝ))
      (ω (algebraMap K L c₀)) with h | h
  · have hc₁ : c₁ ≠ 0 := by
      rintro rfl
      rw [map_zero, ω.map_zero, WithTop.top_add, top_le_iff, ω.top_iff,
        map_eq_zero_iff _ (algebraMap K L).injective] at h
      subst h
      apply hy
      rw [hyt]
      simp
    obtain ⟨m, hm⟩ := hω.base_int c₁ hc₁
    refine ⟨m, ?_⟩
    rw [hyt, ω.map_mul, hω.omega_add_mul_uniformizer, min_eq_right h, hω.omega_traceOneMax, hm,
      ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_eq_coe]
    ring
  · exfalso
    have hc₀ : c₀ ≠ 0 := by
      rintro rfl
      rw [map_zero, ω.map_zero] at h
      exact not_top_lt h
    obtain ⟨a, ha⟩ := exists_omega_eq_coe ω ((map_ne_zero (algebraMap K L)).mpr hc₀)
    have hc₀' : algebraMap K L c₀ ≠ 0 := (map_ne_zero _).mpr hc₀
    have hx' : (hω.traceOneMax - algebraMap K L c₀⁻¹ * y) +
        σ (hω.traceOneMax - algebraMap K L c₀⁻¹ * y) = 1 := by
      rw [map_sub, map_mul, AlgEquiv.commutes, hσy]
      linear_combination hω.traceOneMax_add
    have hx'eq : hω.traceOneMax - algebraMap K L c₀⁻¹ * y =
        -((algebraMap K L c₀)⁻¹ * (hω.traceOneMax *
          (algebraMap K L c₁ * hω.uniformizer))) := by
      rw [hyt, map_inv₀]
      field_simp
      ring
    have hle := hω.omega_le_mu hx'
    have hinv : ω (algebraMap K L c₀)⁻¹ = ((-a : ℝ) : WithTop ℝ) := by
      rw [← zpow_neg_one, omega_zpow ω hc₀' a ha]
      norm_num
    rw [hx'eq, ω.map_neg, ω.map_mul, ω.map_mul, ω.map_mul, hω.omega_uniformizer, hinv,
      hω.omega_traceOneMax] at hle
    rw [ha] at h
    generalize ω (algebraMap K L c₁) = X at h hle
    induction X with
    | top => simp at hle
    | coe b =>
      rw [← WithTop.coe_add] at h
      rw [← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hle
      rw [WithTop.coe_lt_coe] at h
      linarith

/-- A trace-zero element of value at least `n + μ` (with `n ∈ ℤ`) has value at least
`n + 1/2 + μ`. -/
theorem traceZero_add_half_le {z : L} (hz : z + σ z = 0) (n : ℤ)
    (h : (((n : ℝ) + mu K L ω : ℝ) : WithTop ℝ) ≤ ω z) :
    (((n : ℝ) + 1 / 2 + mu K L ω : ℝ) : WithTop ℝ) ≤ ω z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [ω.map_zero]
    exact le_top
  obtain ⟨m, hm⟩ := hω.traceZero_parity hz0 hz
  rw [hm, WithTop.coe_le_coe] at h ⊢
  have h1 : (n : ℝ) < m + 1 := by linarith
  have h2 : n < m + 1 := by exact_mod_cast h1
  have h3 : (n : ℝ) ≤ m := by exact_mod_cast (by omega : n ≤ m)
  linarith

/-- The converse inclusion of Lemma 2.8.1(2): every value in `ℤ + 1/2 + μ` is the value of a
trace-zero element. -/
theorem exists_traceZero_omega_eq (m : ℤ) :
    ∃ y : L, y + σ y = 0 ∧ ω y = (((m : ℝ) + 1 / 2 + mu K L ω : ℝ) : WithTop ℝ) := by
  obtain ⟨m₀, hm₀⟩ :=
    hω.traceZero_parity (traceZeroElement_ne_zero K L) (traceZeroElement_add K L)
  refine ⟨algebraMap K L (hω.baseUniformizer ^ (m - m₀)) * traceZeroElement K L, ?_, ?_⟩
  · rw [map_mul, AlgEquiv.commutes]
    linear_combination algebraMap K L (hω.baseUniformizer ^ (m - m₀)) *
      traceZeroElement_add K L
  · rw [ω.map_mul, hω.omega_baseUniformizer_zpow, hm₀, ← WithTop.coe_add, WithTop.coe_eq_coe]
    push_cast
    ring

/-- The easy direction of Lemma 3.2.2: if `ω(u) ≥ r` then `λ u σ(u)` has value at least
`2r + μ`. -/
theorem le_omega_traceOneMax_mul (r : ℝ) {u : L} (hu : (r : WithTop ℝ) ≤ ω u) :
    ((2 * r + mu K L ω : ℝ) : WithTop ℝ) ≤ ω (hω.traceOneMax * (u * σ u)) := by
  rw [ω.map_mul, ω.map_mul, hω.conjugation_eq, hω.omega_traceOneMax]
  calc ((2 * r + mu K L ω : ℝ) : WithTop ℝ)
      = ((mu K L ω : ℝ) : WithTop ℝ) + ((r : WithTop ℝ) + (r : WithTop ℝ)) := by
        rw [← WithTop.coe_add, ← WithTop.coe_add]
        congr 1
        ring
    _ ≤ _ := add_le_add le_rfl (add_le_add hu hu)

/-- Kaletha–Prasad Lemma 3.2.2, ramified case: if `v + σ(v) = u σ(u)` and
`ω(v) ≥ 2r + μ`, then `ω(u) ≥ r`. -/
theorem le_omega_of_le_omega_second {u v : L} (huv : v + σ v = u * σ u) (r : ℝ)
    (hv : ((2 * r + mu K L ω : ℝ) : WithTop ℝ) ≤ ω v) : (r : WithTop ℝ) ≤ ω u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [ω.map_zero]
    exact le_top
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_conjugation_eq K L (x := u * σ u)
    (by rw [map_mul, conjugation_involutive K L u, mul_comm])
  have hσu : σ u ≠ 0 := by
    intro h
    exact hu0 ((map_eq_zero_iff _ (conjugation K L).injective).mp h)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact mul_ne_zero hu0 hσu hc.symm
  obtain ⟨n, hn⟩ := hω.base_int c hc0
  obtain ⟨t, ht⟩ := exists_omega_eq_coe ω hu0
  have h2t : ((n : ℝ)) = t + t := by
    have h2 : ω (u * σ u) = ((t + t : ℝ) : WithTop ℝ) := by
      rw [ω.map_mul, hω.conjugation_eq, ht, WithTop.coe_add]
    rw [← hc, hn, WithTop.coe_eq_coe] at h2
    exact h2
  rw [ht, WithTop.coe_le_coe]
  by_contra hlt
  rw [not_le] at hlt
  -- `w = λ u σ(u)` has value `μ + n < ω(v)`, and `v - w` has trace zero.
  have hw : ω (hω.traceOneMax * algebraMap K L c) = ((mu K L ω + n : ℝ) : WithTop ℝ) := by
    rw [ω.map_mul, hω.omega_traceOneMax, hn, WithTop.coe_add]
  have hwv : ω (hω.traceOneMax * algebraMap K L c) < ω v := by
    refine lt_of_lt_of_le ?_ hv
    rw [hw, WithTop.coe_lt_coe]
    linarith
  have hx : (v - hω.traceOneMax * algebraMap K L c) +
      σ (v - hω.traceOneMax * algebraMap K L c) = 0 := by
    rw [map_sub, map_mul, AlgEquiv.commutes, hc]
    linear_combination huv - u * σ u * hω.traceOneMax_add
  have hxv : ω (v - hω.traceOneMax * algebraMap K L c) = ((mu K L ω + n : ℝ) : WithTop ℝ) := by
    rw [ω.map_sub_eq_of_lt_right hwv, hw]
  have hx0 : v - hω.traceOneMax * algebraMap K L c ≠ 0 := by
    intro h
    rw [h, ω.map_zero] at hxv
    exact WithTop.top_ne_coe hxv
  obtain ⟨m, hm⟩ := hω.traceZero_parity hx0 hx
  rw [hxv, WithTop.coe_eq_coe] at hm
  exact int_ne_int_add_half n m (by linarith)

/-! ### The lattices `Y_r` and `Z_s` -/

/-- The value of `d ϖ^⌈t⌉` is at least `t` exactly when `d` is integral. -/
theorem le_omega_mul_zpow_ceil_iff (t : ℝ) (d : K) :
    (t : WithTop ℝ) ≤ ω (algebraMap K L (d * hω.baseUniformizer ^ ⌈t⌉)) ↔
      0 ≤ ω (algebraMap K L d) := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  obtain ⟨n, hn⟩ := hω.base_int d hd
  rw [map_mul, ω.map_mul, hω.omega_baseUniformizer_zpow, hn, ← WithTop.coe_add,
    WithTop.coe_le_coe, ← WithTop.coe_zero, WithTop.coe_le_coe, le_int_add_ceil_iff,
    Int.cast_nonneg_iff]

/-- The units `ϖ^⌈r⌉` and `ϖ^⌈r - 1/2⌉` scaling the basis `(1, π)` to a basis of `Y_r`. -/
def latticeUnits (r : ℝ) : Fin 2 → Kˣ :=
  ![Units.mk0 (hω.baseUniformizer ^ ⌈r⌉) (zpow_ne_zero _ hω.baseUniformizer_ne_zero),
    Units.mk0 (hω.baseUniformizer ^ ⌈r - 1 / 2⌉) (zpow_ne_zero _ hω.baseUniformizer_ne_zero)]

/-- The basis `(ϖ^⌈r⌉, ϖ^⌈r - 1/2⌉ π)` of `L` over `K`, an `𝒪`-basis of
`Y_r = {u | ω(u) ≥ r}`. -/
def latticeBasis (r : ℝ) : Module.Basis (Fin 2) K L :=
  hω.uniformizerBasis.unitsSMul (hω.latticeUnits r)

theorem latticeBasis_zero (r : ℝ) :
    hω.latticeBasis r 0 = algebraMap K L (hω.baseUniformizer ^ ⌈r⌉) := by
  rw [latticeBasis, Module.Basis.unitsSMul_apply, uniformizerBasis_zero, Units.smul_def,
    Algebra.smul_def, mul_one]
  rfl

theorem latticeBasis_one (r : ℝ) :
    hω.latticeBasis r 1 =
      algebraMap K L (hω.baseUniformizer ^ ⌈r - 1 / 2⌉) * hω.uniformizer := by
  rw [latticeBasis, Module.Basis.unitsSMul_apply, uniformizerBasis_one, Units.smul_def,
    Algebra.smul_def]
  rfl

/-- The element with coordinates `d₀, d₁` in `latticeBasis r`. -/
theorem latticeBasis_decomposition (r : ℝ) (u : L) :
    u = algebraMap K L ((hω.latticeBasis r).repr u 0 * hω.baseUniformizer ^ ⌈r⌉) +
      algebraMap K L ((hω.latticeBasis r).repr u 1 * hω.baseUniformizer ^ ⌈r - 1 / 2⌉) *
        hω.uniformizer := by
  conv_lhs => rw [← (hω.latticeBasis r).sum_repr u]
  rw [Fin.sum_univ_two, latticeBasis_zero, latticeBasis_one, Algebra.smul_def,
    Algebra.smul_def, map_mul, map_mul]
  ring

/-- `Y_r` is the `𝒪`-span of `latticeBasis r`: `ω(u) ≥ r` exactly when both coordinates of
`u` are integral. This holds for every real `r`. -/
theorem le_omega_iff_latticeBasis (r : ℝ) (u : L) :
    (r : WithTop ℝ) ≤ ω u ↔ ∀ i, 0 ≤ ω (algebraMap K L ((hω.latticeBasis r).repr u i)) := by
  conv_lhs => rw [hω.latticeBasis_decomposition r u]
  rw [hω.omega_add_mul_uniformizer, le_min_iff, coe_le_add_coe_iff,
    hω.le_omega_mul_zpow_ceil_iff, hω.le_omega_mul_zpow_ceil_iff, Fin.forall_fin_two]

theorem le_omega_latticeBasis (r : ℝ) (i : Fin 2) : (r : WithTop ℝ) ≤ ω (hω.latticeBasis r i) := by
  rw [hω.le_omega_iff_latticeBasis, Module.Basis.repr_self]
  intro j
  rw [Finsupp.single_apply]
  split_ifs
  · rw [map_one, ω.map_one]
  · rw [map_zero, ω.map_zero]
    exact le_top

/-- The value of `f₀`, a half-integer. -/
def traceZeroValue : ℝ :=
  ((hω.exists_half_integer (traceZeroElement_ne_zero K L)).choose : ℝ) / 2

theorem omega_traceZeroElement :
    ω (traceZeroElement K L) = ((hω.traceZeroValue : ℝ) : WithTop ℝ) :=
  (hω.exists_half_integer (traceZeroElement_ne_zero K L)).choose_spec

/-- The generator `ϖ^⌈s + μ - ω(f₀)⌉ f₀` of `Z_s = {z | z + σ(z) = 0, ω(z) ≥ s + μ}`. -/
def latticeCenter (s : ℝ) : L :=
  algebraMap K L (hω.baseUniformizer ^ ⌈s + mu K L ω - hω.traceZeroValue⌉) *
    traceZeroElement K L

theorem latticeCenter_ne_zero (s : ℝ) : hω.latticeCenter s ≠ 0 :=
  mul_ne_zero ((map_ne_zero _).mpr (zpow_ne_zero _ hω.baseUniformizer_ne_zero))
    (traceZeroElement_ne_zero K L)

theorem latticeCenter_add (s : ℝ) : hω.latticeCenter s + σ (hω.latticeCenter s) = 0 := by
  rw [latticeCenter, map_mul, AlgEquiv.commutes]
  linear_combination algebraMap K L (hω.baseUniformizer ^ ⌈s + mu K L ω - hω.traceZeroValue⌉) *
    (traceZeroElement_add K L)

/-- `Z_s` is the `𝒪`-span of `latticeCenter s`: `c · latticeCenter s` has value at least
`s + μ` exactly when `c ∈ K` is integral. -/
theorem le_omega_mul_latticeCenter_iff (s : ℝ) (c : K) :
    ((s + mu K L ω : ℝ) : WithTop ℝ) ≤ ω (algebraMap K L c * hω.latticeCenter s) ↔
      0 ≤ ω (algebraMap K L c) := by
  rw [latticeCenter, ← mul_assoc, ← map_mul, ω.map_mul, hω.omega_traceZeroElement,
    coe_le_add_coe_iff, hω.le_omega_mul_zpow_ceil_iff]

/-- Every trace-zero element is a `K`-multiple of `latticeCenter s`. -/
theorem exists_mul_latticeCenter (s : ℝ) {z : L} (hz : z + σ z = 0) :
    ∃ c : K, algebraMap K L c * hω.latticeCenter s = z :=
  exists_algebraMap_mul_eq_of_traceZero K L (hω.latticeCenter_ne_zero s)
    (hω.latticeCenter_add s) hz

/-! ### Integrality of the correction -/

/-- If `ω(x), ω(y) ≥ r` then the correction `σ(λ) x σ(y) − λ σ(x) y` has value at least
`2r + μ`. -/
theorem le_omega_correction (r : ℝ) {x y : L} (hx : (r : WithTop ℝ) ≤ ω x)
    (hy : (r : WithTop ℝ) ≤ ω y) :
    ((2 * r + mu K L ω : ℝ) : WithTop ℝ) ≤ ω (correction K L hω.traceOneMax x y) := by
  have key : ∀ a b c : L, ω a = ((mu K L ω : ℝ) : WithTop ℝ) → (r : WithTop ℝ) ≤ ω b →
      (r : WithTop ℝ) ≤ ω c → ((2 * r + mu K L ω : ℝ) : WithTop ℝ) ≤ ω (a * b * c) := by
    intro a b c ha hb hc
    rw [ω.map_mul, ω.map_mul, ha]
    calc ((2 * r + mu K L ω : ℝ) : WithTop ℝ)
        = ((mu K L ω : ℝ) : WithTop ℝ) + (r : WithTop ℝ) + (r : WithTop ℝ) := by
          rw [← WithTop.coe_add, ← WithTop.coe_add]
          congr 1
          ring
      _ ≤ _ := add_le_add (add_le_add le_rfl hb) hc
  have h1 := key (σ hω.traceOneMax) x (σ y) (by rw [hω.conjugation_eq, hω.omega_traceOneMax])
    hx (by rwa [hω.conjugation_eq])
  have h2 := key hω.traceOneMax (σ x) y hω.omega_traceOneMax (by rwa [hω.conjugation_eq]) hy
  exact le_trans (le_min h1 h2) (ω.map_sub _ _)

/-- For `2r ∈ ℤ` and `s ≤ 2r + 1/2`, the correction of two elements of `Y_r` lies in `Z_s`
(it has trace zero by `correction_add_conjugation`). -/
theorem le_omega_correction_of_le (r s : ℝ) (n : ℤ) (hn : 2 * r = n) (hs : s ≤ 2 * r + 1 / 2)
    {x y : L} (hx : (r : WithTop ℝ) ≤ ω x) (hy : (r : WithTop ℝ) ≤ ω y) :
    ((s + mu K L ω : ℝ) : WithTop ℝ) ≤ ω (correction K L hω.traceOneMax x y) := by
  have h := hω.le_omega_correction r hx hy
  rw [hn] at h
  refine le_trans ?_ (hω.traceZero_add_half_le (correction_add_conjugation K L _ x y) n h)
  rw [WithTop.coe_le_coe]
  linarith

/-- The coordinate chart of `X_{r,s}`: basis `latticeBasis r` (reindexed by `ULift (Fin 2)`),
trace-one element `λ = traceOneMax`, and scalar generator `latticeCenter s`. -/
def latticeData (r s : ℝ) : CoordinateData K L (ULift.{w} (Fin 2)) :=
  CoordinateData.ofBasis K L ((hω.latticeBasis r).reindex Equiv.ulift.symm) hω.traceOneMax
    hω.traceOneMax_add (hω.latticeCenter s) (hω.latticeCenter_ne_zero s) (hω.latticeCenter_add s)

@[simp] theorem latticeData_basis (r s : ℝ) (i : ULift.{w} (Fin 2)) :
    (hω.latticeData r s).basis i = hω.latticeBasis r i.down := by
  simp [latticeData, CoordinateData.ofBasis]

@[simp] theorem latticeData_traceOne (r s : ℝ) :
    (hω.latticeData r s : CoordinateData K L (ULift.{w} (Fin 2))).traceOne = hω.traceOneMax :=
  rfl

@[simp] theorem latticeData_center (r s : ℝ) :
    (hω.latticeData r s : CoordinateData K L (ULift.{w} (Fin 2))).center = hω.latticeCenter s :=
  rfl

/-- For `2r ∈ ℤ` and `s ≤ 2r + 1/2`, the cocycle coefficients of `latticeData r s` are
integral. -/
theorem omega_latticeData_coeff_nonneg (r s : ℝ) (n : ℤ) (hn : 2 * r = n)
    (hs : s ≤ 2 * r + 1 / 2) (i j : ULift.{w} (Fin 2)) :
    0 ≤ ω (algebraMap K L ((hω.latticeData r s).coeff i j)) := by
  have h := (hω.latticeData r s).coeff_mul_center i j
  rw [latticeData_center, latticeData_traceOne, latticeData_basis, latticeData_basis] at h
  rw [← hω.le_omega_mul_latticeCenter_iff s, h]
  exact hω.le_omega_correction_of_le r s n hn hs (hω.le_omega_latticeBasis r _)
    (hω.le_omega_latticeBasis r _)

end IsRamifiedQuadraticValuation

end Lattices

end Langlands.GroupScheme.SU3Root
