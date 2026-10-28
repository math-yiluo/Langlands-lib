import Langlands.Representation.Exponents.DualCharacterMaximalLayerStatement

/-! Proof of the algebraic maximal-layer statement for dual-character quotients. -/

noncomputable section

namespace Langlands

universe uG uH uV

namespace DualCharacterMaximalLayer

section Vandermonde

open Matrix in
/-- A polynomial in a natural parameter, of degree at most `d`, that vanishes at
`0, …, d` has zero coefficients, in any algebra over a field of characteristic zero. -/
theorem coeff_eq_zero_of_eval_nat (K : Type*) {A : Type*} [Field K] [CharZero K] [Ring A]
    [Algebra K A] (d : ℕ) (c : Fin (d + 1) → A)
    (h : ∀ n : Fin (d + 1), ∑ p : Fin (d + 1), ((n : ℕ) : A) ^ (p : ℕ) * c p = 0) :
    c = 0 := by
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) K :=
    Matrix.vandermonde fun n : Fin (d + 1) => ((n : ℕ) : K)
  have hdet : IsUnit M.det := by
    refine isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr ?_)
    intro i j hij
    exact Fin.val_injective (Nat.cast_injective hij)
  have hM : M.map (algebraMap K A) *ᵥ c = 0 := by
    funext n
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M, Matrix.vandermonde_apply,
      map_pow, map_natCast, Pi.zero_apply]
    exact h n
  calc c = (M⁻¹ * M).map (algebraMap K A) *ᵥ c := by
        rw [Matrix.nonsing_inv_mul M hdet, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.one_mulVec]
    _ = M⁻¹.map (algebraMap K A) *ᵥ (M.map (algebraMap K A) *ᵥ c) := by
        rw [Matrix.map_mul, Matrix.mulVec_mulVec]
    _ = 0 := by rw [hM, Matrix.mulVec_zero]

end Vandermonde

section Layers

variable {A : Type*} [CommRing A] (x y : A)

-- The ideal spanned by the monomials of total degree at least `k`.
set_option hygiene false in
local notation "𝓕" k => Ideal.span {t | ∃ i j : ℕ, k ≤ i + j ∧ t = x ^ i * y ^ j}

theorem monomial_mem {k i j : ℕ} (h : k ≤ i + j) : x ^ i * y ^ j ∈ 𝓕 k :=
  Ideal.subset_span ⟨i, j, h, rfl⟩

theorem layer_antitone {k l : ℕ} (h : k ≤ l) : (𝓕 l) ≤ 𝓕 k :=
  Ideal.span_mono fun _ ⟨i, j, hij, ht⟩ => ⟨i, j, h.trans hij, ht⟩

theorem layer_mul_le (k l : ℕ) : (𝓕 k) * (𝓕 l) ≤ 𝓕 (k + l) := by
  rw [Ideal.span_mul_span]
  apply Ideal.span_mono
  rintro _ ⟨_, ⟨i, j, hij, rfl⟩, _, ⟨i', j', hij', rfl⟩, rfl⟩
  exact ⟨i + i', j + j', by omega, by ring⟩

theorem mul_mem_layer {k l : ℕ} {s t : A} (hs : s ∈ 𝓕 k) (ht : t ∈ 𝓕 l) :
    s * t ∈ 𝓕 (k + l) :=
  layer_mul_le x y k l (Ideal.mul_mem_mul hs ht)

theorem pow_mem_layer {s : A} (hs : s ∈ 𝓕 1) (k : ℕ) : s ^ k ∈ 𝓕 k := by
  induction k with
  | zero => simpa using monomial_mem x y (k := 0) (i := 0) (j := 0) le_rfl
  | succ k ih => rw [pow_succ]; exact mul_mem_layer x y ih hs

theorem x_mem_layer_one : x ∈ 𝓕 1 := by
  simpa using monomial_mem x y (k := 1) (i := 1) (j := 0) le_rfl

theorem y_mem_layer_one : y ∈ 𝓕 1 := by
  simpa using monomial_mem x y (k := 1) (i := 0) (j := 1) le_rfl

/-- `(1 + x)^n` agrees with `1 + n x` up to degree two. -/
theorem one_add_pow_sub_mem (n : ℕ) : (1 + x) ^ n - 1 - (n : A) * x ∈ 𝓕 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hx2 : (n : A) * x ^ 2 ∈ 𝓕 2 :=
        Ideal.mul_mem_left _ _ (by simpa using monomial_mem x y (k := 2) (i := 2) (j := 0) le_rfl)
      have := Ideal.add_mem _ (Ideal.mul_mem_right (1 + x) _ ih) hx2
      convert this using 1
      push_cast
      ring

/-- The element `(1 + x)^n (1 + y) - 1` agrees with `n x + y` up to degree two. -/
theorem shifted_sub_linear_mem (n : ℕ) :
    ((1 + x) ^ n * (1 + y) - 1) - ((n : A) * x + y) ∈ 𝓕 2 := by
  have hxy : (n : A) * (x * y) ∈ 𝓕 2 :=
    Ideal.mul_mem_left _ _ (by simpa using monomial_mem x y (k := 2) (i := 1) (j := 1) le_rfl)
  have := Ideal.add_mem _ (Ideal.mul_mem_right (1 + y) _ (one_add_pow_sub_mem x y n)) hxy
  convert this using 1
  ring

theorem linear_mem (n : ℕ) : (n : A) * x + y ∈ 𝓕 1 :=
  Ideal.add_mem _ (Ideal.mul_mem_left _ _ (x_mem_layer_one x y)) (y_mem_layer_one x y)

theorem shifted_mem (n : ℕ) : (1 + x) ^ n * (1 + y) - 1 ∈ 𝓕 1 := by
  have := Ideal.add_mem _ (layer_antitone x y (by norm_num : 1 ≤ 2)
    (shifted_sub_linear_mem x y n)) (linear_mem x y n)
  simpa using this

/-- The `d`-th powers of `(1 + x)^n (1 + y) - 1` and `n x + y` agree up to degree `d + 1`. -/
theorem shifted_pow_sub_linear_pow_mem {d : ℕ} (hd : 0 < d) (n : ℕ) :
    ((1 + x) ^ n * (1 + y) - 1) ^ d - ((n : A) * x + y) ^ d ∈ 𝓕 (d + 1) := by
  rw [← geom_sum₂_mul]
  have hsum : (∑ i ∈ Finset.range d, ((1 + x) ^ n * (1 + y) - 1) ^ i *
      ((n : A) * x + y) ^ (d - 1 - i)) ∈ 𝓕 (d - 1) := by
    refine Ideal.sum_mem _ fun i hi => ?_
    have hi : i < d := Finset.mem_range.mp hi
    have := mul_mem_layer x y (pow_mem_layer x y (shifted_mem x y n) i)
      (pow_mem_layer x y (linear_mem x y n) (d - 1 - i))
    rwa [show i + (d - 1 - i) = d - 1 by omega] at this
  have := mul_mem_layer x y hsum (shifted_sub_linear_mem x y n)
  rwa [show d - 1 + 2 = d + 1 by omega] at this

/-- Downward step: if every monomial of degree above `m ≥ d` vanishes, then so does
every monomial of degree `m`. The relations `((1 + x)^n (1 + y) - 1)^d = 0` give
`y^(m - d) (n x + y)^d = 0` for all `n`, and a Vandermonde argument separates the
binomial terms. -/
theorem layer_eq_bot_of_succ (K : Type*) [Field K] [CharZero K] [Algebra K A]
    {d m : ℕ} (hd : 0 < d) (hdm : d ≤ m) (hm : (𝓕 (m + 1)) = ⊥) (hx : x ^ d = 0)
    (hz : ∀ n : ℕ, ((1 + x) ^ n * (1 + y) - 1) ^ d = 0) : (𝓕 m) = ⊥ := by
  have hlin : ∀ n : ℕ, y ^ (m - d) * ((n : A) * x + y) ^ d = 0 := by
    intro n
    have h := mul_mem_layer x y (pow_mem_layer x y (y_mem_layer_one x y) (m - d))
      (shifted_pow_sub_linear_pow_mem x y hd n)
    rw [show m - d + (d + 1) = m + 1 by omega, hm, Ideal.mem_bot, hz n, zero_sub, mul_neg,
      neg_eq_zero] at h
    exact h
  have hcoeff := coeff_eq_zero_of_eval_nat K d
    (fun p : Fin (d + 1) => ((d.choose p : ℕ) : A) * (x ^ (p : ℕ) * y ^ (d - p) * y ^ (m - d)))
    (fun n => by
      refine (Fin.sum_univ_eq_sum_range (fun p => ((n : ℕ) : A) ^ p *
        (((d.choose p : ℕ) : A) * (x ^ p * y ^ (d - p) * y ^ (m - d)))) (d + 1)).trans ?_
      rw [← hlin n, add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring)
  have hmono : ∀ i, i ≤ d → x ^ i * y ^ (d - i) * y ^ (m - d) = 0 := by
    intro i hi
    have h := congr_fun hcoeff ⟨i, Nat.lt_succ_of_le hi⟩
    simp only [Pi.zero_apply] at h
    have hC : ((d.choose i : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hi).ne'
    calc x ^ i * y ^ (d - i) * y ^ (m - d)
        = algebraMap K A (((d.choose i : ℕ) : K)⁻¹ * ((d.choose i : ℕ) : K)) *
            (x ^ i * y ^ (d - i) * y ^ (m - d)) := by
          rw [inv_mul_cancel₀ hC, map_one, one_mul]
      _ = algebraMap K A (((d.choose i : ℕ) : K)⁻¹) *
            (((d.choose i : ℕ) : A) * (x ^ i * y ^ (d - i) * y ^ (m - d))) := by
          rw [map_mul, map_natCast, mul_assoc]
      _ = 0 := by rw [h, mul_zero]
  rw [eq_bot_iff, Ideal.span_le]
  rintro _ ⟨i, j, hij, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_bot]
  rcases lt_or_eq_of_le hij with hlt | heq
  · have h := monomial_mem x y (k := m + 1) (i := i) (j := j) hlt
    rwa [hm, Ideal.mem_bot] at h
  · rcases le_or_gt d i with hi | hi
    · rw [show i = d + (i - d) by omega, pow_add, hx, zero_mul, zero_mul]
    · rw [show j = (d - i) + (m - d) by omega, pow_add, ← mul_assoc]
      exact hmono i hi.le

/-- Every monomial of degree at least `2d` vanishes when `x^d = y^d = 0`. -/
theorem layer_eq_bot_of_le {d m : ℕ} (hx : x ^ d = 0) (hy : y ^ d = 0) (hm : 2 * d ≤ m) :
    (𝓕 m) = ⊥ := by
  rw [eq_bot_iff, Ideal.span_le]
  rintro _ ⟨i, j, hij, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_bot]
  rcases le_or_gt d i with hi | hi
  · rw [show i = d + (i - d) by omega, pow_add, hx, zero_mul, zero_mul]
  · rw [show j = d + (j - d) by omega, pow_add, hy, zero_mul, mul_zero]

/-- Every monomial of degree at least `d` vanishes. -/
theorem layer_eq_bot (K : Type*) [Field K] [CharZero K] [Algebra K A] {d : ℕ} (hd : 0 < d)
    (hx : x ^ d = 0) (hz : ∀ n : ℕ, ((1 + x) ^ n * (1 + y) - 1) ^ d = 0) : (𝓕 d) = ⊥ := by
  have hy : y ^ d = 0 := by simpa using hz 0
  have key : ∀ t m, d ≤ m → 2 * d ≤ m + t → (𝓕 m) = ⊥ := by
    intro t
    induction t with
    | zero => intro m _ hm; exact layer_eq_bot_of_le x y hx hy hm
    | succ t ih =>
        intro m hdm hm
        exact layer_eq_bot_of_succ x y K hd hdm (ih (m + 1) (by omega) (by omega)) hx hz
  exact key d d le_rfl (by omega)

/-- In a commutative algebra over a field of characteristic zero, if `x^d = 0` and
`((1 + x)^n (1 + y) - 1)^d = 0` for every natural `n`, then `x^(d - 1) y = 0`. -/
theorem pow_pred_mul_eq_zero (K : Type*) [Field K] [CharZero K] [Algebra K A] {d : ℕ}
    (hd : 0 < d) (hx : x ^ d = 0) (hz : ∀ n : ℕ, ((1 + x) ^ n * (1 + y) - 1) ^ d = 0) :
    x ^ (d - 1) * y = 0 := by
  have h := monomial_mem x y (k := d) (i := d - 1) (j := 1) (by omega)
  rwa [layer_eq_bot x y K hd hx hz, Ideal.mem_bot, pow_one] at h

end Layers

section Generic

variable {H : Type*} [CommGroup H] {E : Type*} [AddCommGroup E] [Module ℂ E]

open scoped IsMulCommutative in
/-- For a representation `σ` of a commutative group on which every defect
`σ b - χ b` is nilpotent of order at most `d`, the product of `d - 1` defects at `a`
with one defect at `c` vanishes. The algebraic lemma is applied in the commutative
subalgebra generated by the operators `σ b`. -/
theorem defect_pow_pred_mul_eq_zero (σ : H →* Module.End ℂ E) (χ : H →* ℂˣ) {d : ℕ}
    (hd : 0 < d) (hnil : ∀ b, (σ b - (χ b : ℂ) • 1) ^ d = 0) (a c : H) :
    (σ a - (χ a : ℂ) • 1) ^ (d - 1) * (σ c - (χ c : ℂ) • 1) = 0 := by
  have hscale : ∀ b, (χ b : ℂ)⁻¹ • σ b - 1 = (χ b : ℂ)⁻¹ • (σ b - (χ b : ℂ) • 1) := by
    intro b
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  have hcomm : (Set.range σ).Pairwise Commute := by
    rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩ -
    change σ b * σ b' = σ b' * σ b
    rw [← map_mul, ← map_mul, mul_comm]
  have := Algebra.isMulCommutative_adjoin ℂ hcomm
  let u : H → Algebra.adjoin ℂ (Set.range σ) := fun b =>
    ⟨(χ b : ℂ)⁻¹ • σ b, Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self b)) _⟩
  have hu : ∀ b, (u b - 1) ^ d = 0 := by
    intro b
    apply Subtype.ext
    change ((χ b : ℂ)⁻¹ • σ b - 1) ^ d = 0
    rw [hscale, smul_pow, hnil, smul_zero]
  have hmul : ∀ n : ℕ, u a ^ n * u c = u (a ^ n * c) := by
    intro n
    apply Subtype.ext
    change ((χ a : ℂ)⁻¹ • σ a) ^ n * ((χ c : ℂ)⁻¹ • σ c) =
      (χ (a ^ n * c) : ℂ)⁻¹ • σ (a ^ n * c)
    rw [map_mul, map_pow, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, smul_pow,
      smul_mul_smul_comm, mul_inv, inv_pow]
  have hB := pow_pred_mul_eq_zero (u a - 1) (u c - 1) ℂ hd (hu a) (fun n => by
    rw [add_sub_cancel, add_sub_cancel, hmul]
    exact hu _)
  have h := congrArg Subtype.val hB
  change ((χ a : ℂ)⁻¹ • σ a - 1) ^ (d - 1) * ((χ c : ℂ)⁻¹ • σ c - 1) = 0 at h
  rw [hscale, hscale, smul_pow, smul_mul_smul_comm] at h
  exact (smul_eq_zero.mp h).resolve_left
    (mul_ne_zero (pow_ne_zero _ (inv_ne_zero (Units.ne_zero _))) (inv_ne_zero (Units.ne_zero _)))

end Generic

section Application

variable {G : Type uG} [Group G] {H : Type uH} [CommGroup H] {V : Type uV} [AddCommGroup V]
  [Module ℂ V] (ρ : Representation ℂ G V) (ι : H →* G) (χ : H →* ℂˣ)

open DualCharacterQuotient

/-- If every central defect has order at most `d` on the generalized dual space, then
`d - 1` defects at `a` following one defect at `c` annihilate that space. -/
theorem transpose_defect_pow_pred_mul_eq_zero {d : ℕ} (hd : 0 < d)
    (hbound : ∀ (b : H) (φ : Module.Dual ℂ V), φ ∈ dualSpace ρ ι χ →
      ((commutativeTranspose (ρ.comp ι) b - (χ b : ℂ) • 1) ^ d) φ = 0)
    (a c : H) (φ : Module.Dual ℂ V) (hφ : φ ∈ dualSpace ρ ι χ) :
    ((commutativeTranspose (ρ.comp ι) a - (χ a : ℂ) • 1) ^ (d - 1))
      ((commutativeTranspose (ρ.comp ι) c - (χ c : ℂ) • 1) φ) = 0 := by
  set T := commutativeTranspose (ρ.comp ι)
  let σ := (dualSpace ρ ι χ).toRepresentation
  have hval : ∀ (b : H) (k : ℕ) (ψ : (dualSpace ρ ι χ).toSubmodule),
      (((σ b - (χ b : ℂ) • 1) ^ k) ψ).val = ((T b - (χ b : ℂ) • 1) ^ k) ψ.val := by
    intro b k
    induction k with
    | zero => intro ψ; rfl
    | succ k ih =>
        intro ψ
        rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
        rfl
  have hnil : ∀ b, (σ b - (χ b : ℂ) • 1) ^ d = 0 := by
    intro b
    refine LinearMap.ext fun ψ => Subtype.ext ?_
    rw [hval, LinearMap.zero_apply]
    exact hbound b ψ.val ψ.property
  have hD := defect_pow_pred_mul_eq_zero σ χ hd hnil a c
  let ψ : (dualSpace ρ ι χ).toSubmodule := ⟨φ, hφ⟩
  have hc : ((σ c - (χ c : ℂ) • 1 : Module.End ℂ _) ψ).val = (T c - (χ c : ℂ) • 1) φ := by
    have h := hval c 1 ψ
    rwa [pow_one, pow_one] at h
  calc ((T a - (χ a : ℂ) • 1) ^ (d - 1)) ((T c - (χ c : ℂ) • 1) φ)
      = ((T a - (χ a : ℂ) • 1) ^ (d - 1))
          ((σ c - (χ c : ℂ) • 1 : Module.End ℂ _) ψ).val := by rw [hc]
    _ = (((σ a - (χ a : ℂ) • 1) ^ (d - 1)) ((σ c - (χ c : ℂ) • 1 : Module.End ℂ _) ψ)).val :=
        (hval a (d - 1) _).symm
    _ = (((σ a - (χ a : ℂ) • 1) ^ (d - 1) * (σ c - (χ c : ℂ) • 1)) ψ).val := rfl
    _ = 0 := by rw [hD]; rfl

end Application

end DualCharacterMaximalLayer

open DualCharacterMaximalLayer DualCharacterQuotient in
/-- A positive exact dual nilpotence order `d` makes some `(d - 1)`-st defect image
nonzero, and every such image carries the scalar central character. -/
theorem dualCharacterMaximalLayer : DualCharacterMaximalLayerStatement.{uG, uH, uV} := by
  intro G _ H _ V _ _ ρ ι hι χ d hd hidx
  have hbound : ∀ (b : H) (φ : Module.Dual ℂ V), φ ∈ dualSpace ρ ι χ →
      ((commutativeTranspose (ρ.comp ι) b - (χ b : ℂ) • 1) ^ d) φ = 0 := by
    intro b φ hφ
    have hle := (commutativeCharacterNilpotenceIndex_le_iff _ χ d).mp hidx.le
    exact (mem_commutativeCharacterSpace _ χ d φ).mp (hle hφ) b
  constructor
  · have hnot : ¬ commutativeCharacterNilpotenceIndex (commutativeTranspose (ρ.comp ι)) χ ≤
        ((d - 1 : ℕ) : ℕ∞) := by
      rw [hidx, Nat.cast_le]
      omega
    rw [commutativeCharacterNilpotenceIndex_le_iff, SetLike.not_le_iff_exists] at hnot
    obtain ⟨φ, hφ, hφn⟩ := hnot
    rw [mem_commutativeCharacterSpace] at hφn
    push Not at hφn
    obtain ⟨a, ha⟩ := hφn
    obtain ⟨v, hv⟩ : ∃ v : V,
        (((commutativeTranspose (ρ.comp ι) a - (χ a : ℂ) • 1) ^ (d - 1)) φ) v ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (LinearMap.ext h)
    refine ⟨a, nontrivial_of_ne (defectRangeMap ρ ι hι χ a (d - 1) v) 0 ?_⟩
    intro h0
    apply hv
    have h1 := congrArg (defectRangeInclusion ρ ι hι χ a (d - 1)) h0
    rw [defectRangeInclusion_map, map_zero] at h1
    have h2 := evaluation_defect_pow_quotientMap ρ ι hι χ a (d - 1) ⟨φ, hφ⟩ v
    rw [h1, map_zero] at h2
    exact h2.symm
  · intro a c w
    obtain ⟨q, hq⟩ := (mem_defectRange ρ ι hι χ a (d - 1) w.val).mp w.property
    obtain ⟨v, rfl⟩ := quotientMap_surjective ρ ι hι χ q
    apply Subtype.ext
    change (quotient ρ ι hι χ).ρ (ι c) w.val = (χ c : ℂ) • w.val
    rw [← sub_eq_zero, ← defect_apply, ← hq, defect_pow_quotientMap,
      ← pow_one (defect ρ ι hι χ c), eq_zero_iff]
    intro φ
    rw [evaluation_defect_pow_quotientMap, pow_one]
    have h2 := commutativeTranspose_defect_pow_apply (ρ.comp ι) a (χ a : ℂ) (d - 1)
      ((commutativeTranspose (ρ.comp ι) c - (χ c : ℂ) • 1) φ.val) v
    rw [transpose_defect_pow_pred_mul_eq_zero ρ ι χ hd hbound a c φ.val φ.property,
      LinearMap.zero_apply] at h2
    exact h2.symm

end Langlands
