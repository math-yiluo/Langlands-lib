import Mathlib

/-! # Binary forms attached to a rank-one lowering curve

Pure linear algebra over fields: from the polynomial matrices of a raising and a
lowering additive map satisfying the rank-one relation on a fixed vector, the
lowering curve has degree at most the coroot weight `m`, and the raising,
lowering and torus actions act on the binary form
`ν(X,Y) = ∑_{d ≤ m} X^(m-d) Y^d w_d` by linear substitutions of `(X,Y)`. -/

noncomputable section

open Polynomial Finset
open scoped Matrix

namespace Langlands.Global.SplitRankOne

section Generic

variable {K : Type*} [Field K] {n : Type*}

/-- The binary form `ν(X,Y) = ∑_{d ≤ m} X^(m-d) Y^d w_d`. -/
def binaryForm (m : ℕ) (w : ℕ → n → K) (X Y : K) : n → K :=
  ∑ d ∈ range (m + 1), (X ^ (m - d) * Y ^ d) • w d

/-- The coordinate polynomial obtained by substituting two polynomials. -/
def binaryFormPoly (m : ℕ) (w : ℕ → n → K) (p q : K[X]) (i : n) : K[X] :=
  ∑ d ∈ range (m + 1), p ^ (m - d) * q ^ d * C (w d i)

theorem eval_binaryFormPoly (m : ℕ) (w : ℕ → n → K) (p q : K[X]) (i : n) (x : K) :
    (binaryFormPoly m w p q i).eval x = binaryForm m w (p.eval x) (q.eval x) i := by
  simp only [binaryFormPoly, binaryForm, eval_finsetSum, eval_mul, eval_pow, eval_C,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Two substituted binary forms agreeing on an infinite set of parameters agree
everywhere. -/
theorem binaryForm_eval_eq_of_infinite (m m' : ℕ) (w w' : ℕ → n → K)
    (p q p' q' : K[X]) (S : Set K) (hS : S.Infinite)
    (h : ∀ x ∈ S, binaryForm m w (p.eval x) (q.eval x) =
      binaryForm m' w' (p'.eval x) (q'.eval x)) (x : K) :
    binaryForm m w (p.eval x) (q.eval x) = binaryForm m' w' (p'.eval x) (q'.eval x) := by
  funext i
  rw [← eval_binaryFormPoly, ← eval_binaryFormPoly]
  congr 1
  refine Polynomial.eq_of_infinite_eval_eq _ _ (hS.mono fun y hy => ?_)
  simp only [Set.mem_ofPred_eq, eval_binaryFormPoly, h y hy]

theorem mulVec_binaryForm [Fintype n] (A : Matrix n n K) (m : ℕ) (w : ℕ → n → K)
    (X Y : K) :
    A *ᵥ binaryForm m w X Y = binaryForm m (fun d => A *ᵥ w d) X Y := by
  simp only [binaryForm, Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem smul_binaryForm (c : K) (m : ℕ) (w : ℕ → n → K) (X Y : K) :
    c • binaryForm m w X Y = binaryForm m (fun d => c • w d) X Y := by
  simp only [binaryForm, Finset.smul_sum, smul_smul, mul_comm c]

/-- Dehomogenization at a nonzero first variable. -/
theorem binaryForm_eq_pow_smul (m : ℕ) (w : ℕ → n → K) {X : K} (hX : X ≠ 0) (Y : K) :
    binaryForm m w X Y = X ^ m • ∑ d ∈ range (m + 1), (Y / X) ^ d • w d := by
  simp only [binaryForm, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : d ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  congr 1
  rw [div_pow, pow_sub₀ X hX hd']
  field_simp

theorem binaryForm_one_left (m : ℕ) (w : ℕ → n → K) (Y : K) :
    binaryForm m w 1 Y = ∑ d ∈ range (m + 1), Y ^ d • w d := by
  rw [binaryForm_eq_pow_smul m w one_ne_zero, one_pow, one_smul]
  simp only [div_one]

theorem binaryForm_zero_one (m : ℕ) (w : ℕ → n → K) :
    binaryForm m w 0 1 = w m := by
  rw [binaryForm, Finset.sum_eq_single m]
  · simp
  · intro d hd hdm
    have hd' : d < m := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)) hdm
    simp [zero_pow (Nat.sub_ne_zero_of_lt hd')]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) h

theorem binaryForm_smul (m : ℕ) (w : ℕ → n → K) (c X Y : K) :
    binaryForm m w (c * X) (c * Y) = c ^ m • binaryForm m w X Y := by
  simp only [binaryForm, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : d ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  congr 1
  rw [mul_pow, mul_pow]
  calc c ^ (m - d) * X ^ (m - d) * (c ^ d * Y ^ d)
      = (c ^ (m - d) * c ^ d) * (X ^ (m - d) * Y ^ d) := by ring
    _ = c ^ m * (X ^ (m - d) * Y ^ d) := by rw [← pow_add, Nat.sub_add_cancel hd']

end Generic

section Curve

variable {k : Type*} [Field k] {n : Type*} [Fintype n]

/-- The polynomial vector `M(X) v`. -/
def curve (M : Matrix n n k[X]) (v : n → k) : n → k[X] :=
  M *ᵥ fun i => C (v i)

/-- The coefficient vectors `w_d` of the curve. -/
def coeffVec (M : Matrix n n k[X]) (v : n → k) (d : ℕ) : n → k :=
  fun i => (curve M v i).coeff d

variable {K : Type*} [Field K] [Algebra k K]

theorem mulVec_map_aeval (M : Matrix n n k[X]) (v : n → k) (t : K) :
    M.map (aeval t) *ᵥ (algebraMap k K ∘ v) = fun i => aeval t (curve M v i) := by
  funext i
  simp only [curve, Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply,
    map_sum, map_mul, aeval_C]

theorem aeval_curve_eq_sum (M : Matrix n n k[X]) (v : n → k) (N : ℕ)
    (hN : ∀ d, N < d → coeffVec M v d = 0) (t : K) :
    (fun i => aeval t (curve M v i)) =
      ∑ d ∈ range (N + 1), t ^ d • (algebraMap k K ∘ coeffVec M v d) := by
  funext i
  have hdeg : (curve M v i).natDegree < N + 1 := by
    refine Nat.lt_succ_of_le ((natDegree_le_iff_coeff_eq_zero).mpr fun d hd => ?_)
    have := congrFun (hN d (by exact_mod_cast hd)) i
    simpa [coeffVec] using this
  conv_lhs => rw [as_sum_range' (curve M v i) (N + 1) hdeg]
  simp only [map_sum, aeval_monomial, Finset.sum_apply, Pi.smul_apply, Function.comp_apply,
    smul_eq_mul, coeffVec]
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

theorem mulVec_map_eval (M : Matrix n n k[X]) (v : n → k) (t : k) :
    M.map (eval t) *ᵥ v = fun i => eval t (curve M v i) := by
  have h := mulVec_map_aeval (K := k) M v t
  simpa [Polynomial.coe_aeval_eq_eval] using h

/-- **Degree bound.** If the raising matrix at `1` and the lowering curve satisfy the
rank-one relation on `v` with coroot weight `m`, then every coefficient of the lowering
curve of degree greater than `m` vanishes. -/
theorem coeffVec_eq_zero_of_relation [Infinite k] (Mp Mm : Matrix n n k[X]) (v : n → k)
    (m : ℤ)
    (hrel : ∀ t : k, 1 + t ≠ 0 →
      Mp.map (eval 1) *ᵥ (Mm.map (eval t) *ᵥ v) =
        (1 + t) ^ m • (Mm.map (eval ((1 + t)⁻¹ * t)) *ᵥ v)) :
    ∀ d : ℕ, m < d → coeffVec Mm v d = 0 := by
  set w := coeffVec Mm v with hw
  set A := Mp.map (eval (1 : k)) with hA
  -- the key step: the top coefficient beyond `m` vanishes
  have claim : ∀ D : ℕ, (∀ d, D < d → w d = 0) → m < D → w D = 0 := by
    intro D hD hmD
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = D - m := ⟨(D - m).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hN1 : 1 ≤ N := by omega
    funext i
    -- the two polynomials
    let L : k[X] := (1 + X) ^ N * ∑ j, C (A i j) * curve Mm v j
    let R : k[X] := ∑ d ∈ range (D + 1), X ^ d * (1 + X) ^ (D - d) * C (w d i)
    have hLR : L = R := by
      refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
      have hinf : ({(-1 : k)}ᶜ : Set k).Infinite := (Set.finite_singleton _).infinite_compl
      refine hinf.mono fun t ht => ?_
      have ht' : 1 + t ≠ 0 := by
        intro h0
        apply ht
        simp only [Set.mem_singleton_iff]
        linear_combination h0
      have hcurve := aeval_curve_eq_sum (K := k) Mm v D hD
      have hrelt := congrFun (hrel t ht') i
      simp only [Set.mem_ofPred_eq, L, R, eval_mul, eval_pow, eval_add, eval_one, eval_X,
        eval_finsetSum, eval_C]
      have hl : ∑ j, A i j * eval t (curve Mm v j) = (A *ᵥ (Mm.map (eval t) *ᵥ v)) i := by
        rw [mulVec_map_eval Mm v t]
        rfl
      rw [hl, hrelt, mulVec_map_eval]
      have hc := congrFun (hcurve ((1 + t)⁻¹ * t)) i
      simp only [Polynomial.coe_aeval_eq_eval] at hc
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hc]
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
        Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' : d ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
      have hpow : (1 + t) ^ N * (1 + t) ^ m = (1 + t) ^ (D : ℤ) := by
        rw [← zpow_natCast, ← zpow_add₀ ht', hN]
        ring_nf
      have hD' : (1 + t) ^ (D : ℤ) * ((1 + t)⁻¹ * t) ^ d = t ^ d * (1 + t) ^ (D - d) := by
        rw [zpow_natCast, mul_pow, inv_pow, ← Nat.sub_add_cancel hd', pow_add]
        field_simp
        rw [Nat.sub_add_cancel hd']
        ring
      calc (1 + t) ^ N * ((1 + t) ^ m * (((1 + t)⁻¹ * t) ^ d * w d i))
          = ((1 + t) ^ N * (1 + t) ^ m) * ((1 + t)⁻¹ * t) ^ d * w d i := by ring
        _ = t ^ d * (1 + t) ^ (D - d) * w d i := by rw [hpow, hD']
    have hev := congrArg (eval (-1 : k)) hLR
    simp only [L, R, eval_mul, eval_pow, eval_add, eval_one, eval_X, eval_finsetSum, eval_C,
      add_neg_cancel, zero_pow (Nat.one_le_iff_ne_zero.mp hN1), zero_mul] at hev
    rw [Finset.sum_eq_single D] at hev
    · simp only [Nat.sub_self, pow_zero, mul_one] at hev
      have hne : ((-1 : k) ^ D) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
      simpa [hne] using hev.symm
    · intro d hd hdD
      have hd' : d < D := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)) hdD
      simp [zero_pow (Nat.sub_ne_zero_of_lt hd')]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self D)) h
  -- a global degree bound
  obtain ⟨D₀, hD₀⟩ : ∃ D₀ : ℕ, ∀ d, D₀ < d → w d = 0 := by
    refine ⟨Finset.univ.sup fun i => (curve Mm v i).natDegree, fun d hd => ?_⟩
    funext i
    have hle : (curve Mm v i).natDegree ≤ Finset.univ.sup fun i => (curve Mm v i).natDegree :=
      Finset.le_sup (f := fun i => (curve Mm v i).natDegree) (Finset.mem_univ i)
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle hd)
  -- downward induction
  have key : ∀ D : ℕ, (∀ d, D < d → w d = 0) → ∀ d : ℕ, m < d → w d = 0 := by
    intro D
    induction D with
    | zero =>
      intro hD d hd
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h
        exact claim 0 hD hd
      · exact hD d h
    | succ D ih =>
      intro hD d hd
      by_cases hmD : m < (D + 1 : ℕ)
      · have hw0 := claim (D + 1) hD hmD
        refine ih (fun d' hd' => ?_) d hd
        rcases Nat.lt_or_ge (D + 1) d' with h | h
        · exact hD d' h
        · have : d' = D + 1 := le_antisymm h hd'
          rw [this]
          exact hw0
      · exact hD d (by push Not at hmD; exact_mod_cast lt_of_le_of_lt hmD hd)
  exact key D₀ hD₀

end Curve

section CellAction

variable {K : Type*} [Field K] {n : Type*} [Fintype n]

/-- Dehomogenization through a lowering curve `M t *ᵥ e = ν(1,t)`. -/
theorem binaryForm_eq_curve (m : ℕ) (w : ℕ → n → K) (M : K → Matrix n n K) (e : n → K)
    (hcurve : ∀ t, M t *ᵥ e = binaryForm m w 1 t) {X : K} (hX : X ≠ 0) (Y : K) :
    binaryForm m w X Y = X ^ m • (M (Y / X) *ᵥ e) := by
  rw [hcurve, ← binaryForm_smul, mul_one, mul_div_cancel₀ Y hX]

variable [Infinite K]

/-- The lowering curve acts on the binary form by `(X,Y) ↦ (X, Y + yX)`. -/
theorem lowering_mulVec_binaryForm (m : ℕ) (w : ℕ → n → K) (M : K → Matrix n n K)
    (e : n → K) (hcurve : ∀ t, M t *ᵥ e = binaryForm m w 1 t)
    (hadd : ∀ s t, M (s + t) = M s * M t) (y X Y : K) :
    M y *ᵥ binaryForm m w X Y = binaryForm m w X (Y + y * X) := by
  rw [mulVec_binaryForm]
  have h := binaryForm_eval_eq_of_infinite m m (fun d => M y *ᵥ w d) w Polynomial.X (C Y)
    Polynomial.X (C Y + C y * Polynomial.X) ({0}ᶜ) (Set.finite_singleton _).infinite_compl
    (fun X hX => ?_) X
  · simpa using h
  · have hX' : X ≠ 0 := hX
    simp only [eval_X, eval_C, eval_add, eval_mul]
    rw [← mulVec_binaryForm, binaryForm_eq_curve m w M e hcurve hX', Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, ← hadd, hcurve, ← binaryForm_smul, mul_one]
    congr 1
    field_simp
    ring

/-- The raising map acts on the binary form by `(X,Y) ↦ (X + zY, Y)`, given the rank-one
relation on the fixed vector `e`. -/
theorem raising_mulVec_binaryForm (m : ℕ) (w : ℕ → n → K) (M P : K → Matrix n n K)
    (e : n → K) (hcurve : ∀ t, M t *ᵥ e = binaryForm m w 1 t)
    (hrel : ∀ s t, 1 + s * t ≠ 0 →
      P s *ᵥ (M t *ᵥ e) = (1 + s * t) ^ m • (M ((1 + s * t)⁻¹ * t) *ᵥ e))
    (z X Y : K) :
    P z *ᵥ binaryForm m w X Y = binaryForm m w (X + z * Y) Y := by
  rw [mulVec_binaryForm]
  have hS : ({X | X ≠ 0 ∧ X + z * Y ≠ 0} : Set K).Infinite := by
    have hfin : ({0, -(z * Y)} : Set K).Finite := (Set.finite_singleton _).insert _
    refine (hfin.infinite_compl).mono fun X hX => ?_
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hX
    refine ⟨hX.1, fun h0 => hX.2 ?_⟩
    linear_combination h0
  have h := binaryForm_eval_eq_of_infinite m m (fun d => P z *ᵥ w d) w Polynomial.X (C Y)
    (Polynomial.X + C z * C Y) (C Y) _ hS (fun X hX => ?_) X
  · simpa using h
  · obtain ⟨hX0, hXz⟩ := hX
    simp only [eval_X, eval_C, eval_add, eval_mul]
    rw [← mulVec_binaryForm, binaryForm_eq_curve m w M e hcurve hX0, Matrix.mulVec_smul]
    have hu : 1 + z * (Y / X) ≠ 0 := by
      rwa [show 1 + z * (Y / X) = (X + z * Y) / X by field_simp, div_ne_zero_iff,
        and_iff_left hX0]
    rw [hrel z (Y / X) hu, hcurve, smul_smul, ← mul_pow, ← binaryForm_smul]
    congr 1
    · field_simp
    · field_simp

/-- A torus element with eigenvalue `c` on `e`, normalizing the lowering curve through
the character value `a`, acts by `(X,Y) ↦ c • ν(X, a⁻¹ Y)`. -/
theorem torus_mulVec_binaryForm (m : ℕ) (w : ℕ → n → K) (M : K → Matrix n n K)
    (e : n → K) (hcurve : ∀ t, M t *ᵥ e = binaryForm m w 1 t)
    (A : Matrix n n K) (c a : K) (he : A *ᵥ e = c • e)
    (hA : ∀ t, A *ᵥ (M t *ᵥ e) = M (a⁻¹ * t) *ᵥ (A *ᵥ e)) (X Y : K) :
    A *ᵥ binaryForm m w X Y = c • binaryForm m w X (a⁻¹ * Y) := by
  rw [mulVec_binaryForm, smul_binaryForm]
  have h := binaryForm_eval_eq_of_infinite m m (fun d => A *ᵥ w d) (fun d => c • w d)
    Polynomial.X (C Y) Polynomial.X (C (a⁻¹ * Y)) ({0}ᶜ)
    (Set.finite_singleton _).infinite_compl (fun X hX => ?_) X
  · simpa using h
  · have hX' : X ≠ 0 := hX
    simp only [eval_X, eval_C]
    rw [← mulVec_binaryForm, ← smul_binaryForm, binaryForm_eq_curve m w M e hcurve hX',
      binaryForm_eq_curve m w M e hcurve hX', Matrix.mulVec_smul, hA, he,
      Matrix.mulVec_smul, smul_comm, mul_div_assoc]

end CellAction

section Similitude

variable {K : Type*} [Field K] {n : Type*} [Fintype n]

/-- The binary form evaluated at a vector of `K²`. -/
def nu (m : ℕ) (w : ℕ → n → K) (x : Fin 2 → K) : n → K :=
  binaryForm m w (x 0) (x 1)

/-- `B` acts on the binary form through a `GL₂`-substitution `h` and a scalar `μ` with
`μ² det(h)^m = c`. -/
def IsBinarySimilitude (m : ℕ) (w : ℕ → n → K) (B : Matrix n n K) (c : K) : Prop :=
  ∃ (h : Matrix (Fin 2) (Fin 2) K) (μ : K), μ ≠ 0 ∧ h.det ≠ 0 ∧ μ ^ 2 * h.det ^ m = c ∧
    ∀ x : Fin 2 → K, B *ᵥ nu m w x = μ • nu m w (h *ᵥ x)

theorem isBinarySimilitude_one [DecidableEq n] (m : ℕ) (w : ℕ → n → K) :
    IsBinarySimilitude m w (1 : Matrix n n K) 1 :=
  ⟨1, 1, one_ne_zero, by simp, by simp, fun x => by simp⟩

theorem IsBinarySimilitude.mul {m : ℕ} {w : ℕ → n → K} {B₁ B₂ : Matrix n n K} {c₁ c₂ : K}
    (h₁ : IsBinarySimilitude m w B₁ c₁) (h₂ : IsBinarySimilitude m w B₂ c₂) :
    IsBinarySimilitude m w (B₁ * B₂) (c₁ * c₂) := by
  obtain ⟨g₁, μ₁, hμ₁, hg₁, hc₁, hB₁⟩ := h₁
  obtain ⟨g₂, μ₂, hμ₂, hg₂, hc₂, hB₂⟩ := h₂
  refine ⟨g₁ * g₂, μ₁ * μ₂, mul_ne_zero hμ₁ hμ₂, by rw [Matrix.det_mul]; exact mul_ne_zero hg₁ hg₂,
    ?_, fun x => ?_⟩
  · rw [Matrix.det_mul, ← hc₁, ← hc₂]
    ring
  · rw [← Matrix.mulVec_mulVec, hB₂, Matrix.mulVec_smul, hB₁, smul_smul, Matrix.mulVec_mulVec,
      mul_comm μ₂ μ₁]

theorem IsBinarySimilitude.inv {m : ℕ} {w : ℕ → n → K} [DecidableEq n]
    {B B' : Matrix n n K} {c : K} (hB : IsBinarySimilitude m w B c) (hBB : B' * B = 1) :
    IsBinarySimilitude m w B' c⁻¹ := by
  obtain ⟨g, μ, hμ, hg, hc, hact⟩ := hB
  have hgu : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  refine ⟨g⁻¹, μ⁻¹, inv_ne_zero hμ, ?_, ?_, fun x => ?_⟩
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hg
  · rw [← hc, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', mul_inv, inv_pow, inv_pow]
  · have h := hact (g⁻¹ *ᵥ x)
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hgu, Matrix.one_mulVec] at h
    have h' := congrArg (fun v => B' *ᵥ v) h
    simp only [Matrix.mulVec_mulVec, hBB, Matrix.one_mulVec, Matrix.mulVec_smul] at h'
    rw [h', smul_smul, inv_mul_cancel₀ hμ, one_smul]

variable [Infinite K]

theorem isBinarySimilitude_lowering (m : ℕ) (w : ℕ → n → K) (M : K → Matrix n n K)
    (e : n → K) (hcurve : ∀ t, M t *ᵥ e = binaryForm m w 1 t)
    (hadd : ∀ s t, M (s + t) = M s * M t) (y : K) :
    IsBinarySimilitude m w (M y) 1 := by
  refine ⟨!![1, 0; y, 1], 1, one_ne_zero, by simp [Matrix.det_fin_two], by
    simp [Matrix.det_fin_two], fun x => ?_⟩
  rw [one_smul, nu, nu, lowering_mulVec_binaryForm m w M e hcurve hadd]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring_nf

theorem isBinarySimilitude_raising (m : ℕ) (w : ℕ → n → K) (M P : K → Matrix n n K)
    (e : n → K) (hcurve : ∀ t, M t *ᵥ e = binaryForm m w 1 t)
    (hrel : ∀ s t, 1 + s * t ≠ 0 →
      P s *ᵥ (M t *ᵥ e) = (1 + s * t) ^ m • (M ((1 + s * t)⁻¹ * t) *ᵥ e)) (z : K) :
    IsBinarySimilitude m w (P z) 1 := by
  refine ⟨!![1, z; 0, 1], 1, one_ne_zero, by simp [Matrix.det_fin_two], by
    simp [Matrix.det_fin_two], fun x => ?_⟩
  rw [one_smul, nu, nu, raising_mulVec_binaryForm m w M P e hcurve hrel]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem isBinarySimilitude_torus (m : ℕ) (w : ℕ → n → K) (M : K → Matrix n n K)
    (e : n → K) (hcurve : ∀ t, M t *ᵥ e = binaryForm m w 1 t)
    (A : Matrix n n K) (c a : K) (hc : c ≠ 0) (ha : a ≠ 0) (he : A *ᵥ e = c • e)
    (hA : ∀ t, A *ᵥ (M t *ᵥ e) = M (a⁻¹ * t) *ᵥ (A *ᵥ e)) :
    IsBinarySimilitude m w A (c ^ 2 * (a⁻¹) ^ m) := by
  refine ⟨!![1, 0; 0, a⁻¹], c, hc, by simp [Matrix.det_fin_two, ha], by
    simp [Matrix.det_fin_two], fun x => ?_⟩
  rw [nu, nu, torus_mulVec_binaryForm m w M e hcurve A c a he hA]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end Similitude

end Langlands.Global.SplitRankOne
