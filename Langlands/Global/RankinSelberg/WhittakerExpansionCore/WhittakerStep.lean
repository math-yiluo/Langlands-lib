import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerDecay

/-! # Summable majorants by induction on the level

`LevelMajorants V ψ m` says that, for an exponent `k` independent of `f`, every `f ∈ V` and every
compact set `C` have nonnegative summable majorants `b T e` on `N_m(F) \ GL_m(F)` of the
Whittaker terms `W_f(diag(γ_q, I) ρ x)`, uniformly in `x ∈ C` and in the rational matrices `ρ` of
height at most `(T, e)`, with total mass at most `A (T e)^k`. Level `0` is the boundedness of `f`
on determinant bands. The passage from level `j` to `j + 1` writes each coset of level `j + 1`
through its last row `ξ` and its remaining coset of level `j`, uses the last-row decay
`(1 + ‖ξ‖)^(-N)`, the integrality of `D₀ e² ξ` on the support and the height of the
representative `γ_ξ`, and sums over the lattice of integral rows. The conclusion is
`WhittakerMajorantsStatement`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints

local instance stepSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance stepSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

open scoped Classical

section Rows

/-- The size `1 + ‖v‖_∞` of a rational row `v`. -/
def rowSize {n : ℕ} (v : Fin n → F) : ℝ :=
  1 + ‖EqualAnalytic.rowEmbedding F n v‖

theorem one_le_rowSize {n : ℕ} (v : Fin n → F) : 1 ≤ rowSize F v :=
  le_add_of_nonneg_right (norm_nonneg _)

theorem rowSize_pos {n : ℕ} (v : Fin n → F) : 0 < rowSize F v :=
  zero_lt_one.trans_le (one_le_rowSize F v)

theorem norm_le_rowSize {n : ℕ} (v : Fin n → F) (i : Fin n) :
    ‖mixedEmbedding F (v i)‖ ≤ rowSize F v :=
  (norm_le_pi_norm (EqualAnalytic.rowEmbedding F n v) i).trans
    (le_add_of_nonneg_left zero_le_one)

theorem rowSize_natCast_mul_le {n M : ℕ} (hM : 0 < M) (v : Fin n → F) :
    rowSize F (fun i => (M : F) * v i) ≤ M * rowSize F v := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h : ‖EqualAnalytic.rowEmbedding F n (fun i => (M : F) * v i)‖ ≤
      M * ‖EqualAnalytic.rowEmbedding F n v‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    exact (norm_mixedEmbedding_natCast_mul_le M (v i)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm (EqualAnalytic.rowEmbedding F n v) i)
        (Nat.cast_nonneg _))
  unfold rowSize
  nlinarith [norm_nonneg (EqualAnalytic.rowEmbedding F n v)]

/-- The representative `rowGL v i` with last row `v` (and `1` for the zero row). -/
def rowGamma {k : ℕ} (v : Fin (k + 1) → F) : RationalGL F (k + 1) :=
  if h : v ≠ 0 then rowGL v (rowPivot v) (rowPivot_spec h) else 1

omit [NumberField F] in
theorem rowGamma_cosetRow {j : ℕ} (q : UnipotentRationalCosets F (j + 1)) :
    rowGamma F (cosetRow F q) = cosetGamma F q := by
  rw [rowGamma, dite_eq_left (cosetRow_ne_zero F q)]
  rfl

/-- A denominator `e₁ ≤ M ‖v‖^d` with `rowGamma (v / M)` of height at most `(M ‖v‖^d, e₁)`,
chosen when it exists (and `1` otherwise). -/
def rowDen (M : ℕ) {k : ℕ} (v : Fin (k + 1) → F) : ℕ :=
  if h : ∃ e₁ : ℕ, 0 < e₁ ∧ (e₁ : ℝ) ≤ M * rowSize F v ^ Module.finrank ℚ F ∧
      HeightLE F (M * rowSize F v ^ Module.finrank ℚ F) e₁ (rowGamma F fun i => v i / M) then
    h.choose
  else 1

theorem rowDen_pos (M : ℕ) {k : ℕ} (v : Fin (k + 1) → F) : 0 < rowDen F M v := by
  unfold rowDen
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_pos

theorem rowDen_le {M : ℕ} (hM : 0 < M) {k : ℕ} (v : Fin (k + 1) → F) :
    (rowDen F M v : ℝ) ≤ M * rowSize F v ^ Module.finrank ℚ F := by
  unfold rowDen
  split_ifs with h
  · exact h.choose_spec.2.1
  · have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    rw [Nat.cast_one]
    exact one_le_mul_of_one_le_of_one_le hM1 (one_le_pow₀ (one_le_rowSize F v))

/-- For a nonzero integral row `v` and a positive integer `M`, the representative of the row
`v / M` has height at most `(M ‖v‖^d, rowDen M v)`. -/
theorem heightLE_rowDen {M : ℕ} (hM : 0 < M) {k : ℕ} {v : Fin (k + 1) → F}
    (hv : v ∈ EqualAnalytic.IntegralRows F (k + 1) 1) (hv0 : v ≠ 0) :
    HeightLE F (M * rowSize F v ^ Module.finrank ℚ F) (rowDen F M v)
      (rowGamma F fun i => v i / M) := by
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hex : ∃ e₁ : ℕ, 0 < e₁ ∧ (e₁ : ℝ) ≤ M * rowSize F v ^ Module.finrank ℚ F ∧
      HeightLE F (M * rowSize F v ^ Module.finrank ℚ F) e₁ (rowGamma F fun i => v i / M) := by
    choose w hw using hv
    have hw' : ∀ i, v i = (w i : F) := fun i => by
      have h := hw i
      rw [map_one, one_mul] at h
      exact h
    have hξ0 : (fun i => v i / M) ≠ 0 := by
      intro h0
      apply hv0
      funext i
      have h1 := congrFun h0 i
      simp only [Pi.zero_apply, div_eq_zero_iff, hMF, or_false] at h1
      exact h1
    obtain ⟨e₁, he₁, hle, hH⟩ := exists_heightLE_rowGL (F := F) hM (ξ := fun i => v i / M) w
      (fun i => by rw [← hw' i]; field_simp) (one_le_rowSize F v)
      (fun i => by rw [← hw' i]; exact norm_le_rowSize F v i) (rowPivot_spec hξ0)
    refine ⟨e₁, he₁, hle, ?_⟩
    rw [rowGamma, dite_eq_left hξ0]
    exact hH
  rw [rowDen, dite_eq_left hex]
  exact hex.choose_spec.2.2

/-- The family `p ↦ ‖p.1‖^(-a) β p.1 p.2` supported on the integral rows. -/
def weightedFamily {X : Type*} (n a : ℕ) (β : (Fin n → F) → X → ℝ) (p : (Fin n → F) × X) : ℝ :=
  if p.1 ∈ EqualAnalytic.IntegralRows F n 1 then (rowSize F p.1 ^ a)⁻¹ * β p.1 p.2 else 0

theorem weightedFamily_nonneg {X : Type*} {n a : ℕ} {β : (Fin n → F) → X → ℝ}
    (hβ0 : ∀ v x, 0 ≤ β v x) (p : (Fin n → F) × X) : 0 ≤ weightedFamily F n a β p := by
  unfold weightedFamily
  split_ifs
  · exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (rowSize_pos F _).le _)) (hβ0 _ _)
  · exact le_rfl

/-- **Lattice summation.** If the fibre sums of `β ≥ 0` over the integral rows grow at most like
`K ‖v‖^a`, then the family weighted by `‖v‖^(-(a+s))` is summable for `s > n d`, with sum at most
`K Σ_v ‖v‖^(-s)`. -/
theorem summable_weightedFamily {X : Type*} {n a s : ℕ} (hs : n * Module.finrank ℚ F < s)
    {β : (Fin n → F) → X → ℝ} (hβ0 : ∀ v x, 0 ≤ β v x) (hβ : ∀ v, Summable (β v)) {K : ℝ}
    (hK : ∀ v ∈ EqualAnalytic.IntegralRows F n 1, ∑' x, β v x ≤ K * rowSize F v ^ a) :
    Summable (weightedFamily F n (a + s) β) ∧
      ∑' p, weightedFamily F n (a + s) β p ≤
        K * ∑' v : EqualAnalytic.IntegralRows F n 1, (rowSize F v.1 ^ s)⁻¹ := by
  have hZ : Summable fun v : EqualAnalytic.IntegralRows F n 1 => (rowSize F v.1 ^ s)⁻¹ := by
    have h := EqualAnalytic.summable_integralRows F n 1 one_ne_zero (r := (s : ℝ))
      (by exact_mod_cast hs)
    refine h.congr fun v => ?_
    change rowSize F v.1 ^ (-(s : ℝ)) = _
    rw [Real.rpow_neg (rowSize_pos F v.1).le, Real.rpow_natCast]
  have hfib : ∀ v, Summable fun x => weightedFamily F n (a + s) β (v, x) := by
    intro v
    by_cases hv : v ∈ EqualAnalytic.IntegralRows F n 1
    · have h1 : (fun x => weightedFamily F n (a + s) β (v, x)) =
          fun x => (rowSize F v ^ (a + s))⁻¹ * β v x := funext fun x => by
        unfold weightedFamily
        exact ite_eq_left hv
      rw [h1]
      exact (hβ v).mul_left _
    · have h1 : (fun x => weightedFamily F n (a + s) β (v, x)) = fun _ => 0 :=
        funext fun x => by
          unfold weightedFamily
          exact ite_eq_right hv
      rw [h1]
      exact summable_zero
  have hfibsum : ∀ v, ∑' x, weightedFamily F n (a + s) β (v, x) ≤
      (EqualAnalytic.IntegralRows F n 1).indicator (fun v => K * (rowSize F v ^ s)⁻¹) v := by
    intro v
    by_cases hv : v ∈ EqualAnalytic.IntegralRows F n 1
    · rw [Set.indicator_of_mem hv]
      have h1 : ∀ x, weightedFamily F n (a + s) β (v, x) =
          (rowSize F v ^ (a + s))⁻¹ * β v x := fun x => by
        unfold weightedFamily
        exact ite_eq_left hv
      rw [tsum_congr h1, tsum_mul_left]
      have hpos := rowSize_pos F v
      calc (rowSize F v ^ (a + s))⁻¹ * ∑' x, β v x ≤
            (rowSize F v ^ (a + s))⁻¹ * (K * rowSize F v ^ a) :=
            mul_le_mul_of_nonneg_left (hK v hv) (inv_nonneg.mpr (pow_nonneg hpos.le _))
        _ = K * (rowSize F v ^ s)⁻¹ := by
            rw [pow_add]
            field_simp
    · rw [Set.indicator_of_notMem hv]
      have h1 : ∀ x, weightedFamily F n (a + s) β (v, x) = 0 := fun x => by
        unfold weightedFamily
        exact ite_eq_right hv
      simp only [h1, tsum_zero, le_refl]
  have hind : Summable ((EqualAnalytic.IntegralRows F n 1).indicator
      (fun v => K * (rowSize F v ^ s)⁻¹)) :=
    (summable_subtype_iff_indicator (f := fun v => K * (rowSize F v ^ s)⁻¹)
      (s := EqualAnalytic.IntegralRows F n 1)).mp (hZ.mul_left K)
  have hfibs : Summable fun v => ∑' x, weightedFamily F n (a + s) β (v, x) :=
    hind.of_nonneg_of_le (fun v => tsum_nonneg fun x => weightedFamily_nonneg F hβ0 _) hfibsum
  have hsum : Summable (weightedFamily F n (a + s) β) :=
    (summable_prod_of_nonneg fun p => weightedFamily_nonneg F hβ0 p).mpr ⟨hfib, hfibs⟩
  refine ⟨hsum, ?_⟩
  rw [hsum.tsum_prod' hfib]
  calc ∑' v, ∑' x, weightedFamily F n (a + s) β (v, x) ≤
        ∑' v, (EqualAnalytic.IntegralRows F n 1).indicator
          (fun v => K * (rowSize F v ^ s)⁻¹) v :=
        Summable.tsum_le_tsum hfibsum hfibs hind
    _ = K * ∑' v : EqualAnalytic.IntegralRows F n 1, (rowSize F v.1 ^ s)⁻¹ := by
        rw [← tsum_subtype, tsum_mul_left]

end Rows

section Induction

/-- The height parameter `(r + 1) M ‖v‖^d T` of `diag(γ_v, I) ρ`. -/
def stepHeight (r M : ℕ) (T : ℝ) {n : ℕ} (v : Fin n → F) : ℝ :=
  ((r + 1 : ℕ) : ℝ) * ((M : ℝ) * rowSize F v ^ Module.finrank ℚ F * T)

/-- The fibre family `M^N c T^(2N) Σ_o b_o(T_v, e_v, ·)` over a row `v`. -/
def stepFamily {O X : Type*} [Fintype O] (r : ℕ) (b : O → ℝ → ℕ → X → ℝ) (c : ℝ) (N M : ℕ)
    (T : ℝ) (e : ℕ) {k : ℕ} (v : Fin (k + 1) → F) (x : X) : ℝ :=
  (M : ℝ) ^ N * c * T ^ (2 * N) * ∑ o, b o (stepHeight F r M T v) (rowDen F M v * e) x

/-- The majorant at level `j + 1`: the weighted family read at `(D₀ e² ξ_q, q')`. -/
def stepMajorant {O : Type*} [Fintype O] (r j : ℕ)
    (b : O → ℝ → ℕ → UnipotentRationalCosets F j → ℝ) (c : ℝ) (N D₀ : ℕ) (T : ℝ) (e : ℕ)
    (q : UnipotentRationalCosets F (j + 1)) : ℝ :=
  weightedFamily F (j + 1) N (stepFamily F r b c N (D₀ * e ^ 2) T e)
    (fun i => ((D₀ * e ^ 2 : ℕ) : F) * cosetRow F q i, cosetRest F q)

variable {r : ℕ} (V : Submodule ℂ (Points F (r + 1) → ℂ)) (ψ : AddChar (Adeles F) ℂ)

/-- Majorants at level `m` with a uniform exponent `k`, for rational translates of height at
most `(T, e)`. -/
def LevelMajorants (m : ℕ) (hm : m ≤ r) : Prop :=
  ∃ k : ℕ, ∀ (f : V) (C : Set (Points F (r + 1))), IsCompact C →
    ∃ (A : ℝ) (b : ℝ → ℕ → UnipotentRationalCosets F m → ℝ), 0 ≤ A ∧
      ∀ T : ℝ, 1 ≤ T → ∀ e : ℕ, 0 < e →
        (∀ q, 0 ≤ b T e q) ∧ Summable (b T e) ∧ ∑' q, b T e q ≤ A * (T * e) ^ k ∧
        ∀ ρ : RationalGL F (r + 1), HeightLE F T e ρ → ∀ q, ∀ x ∈ C,
          ‖whittaker F r ψ (f : Points F (r + 1) → ℂ)
            (padRational F (Nat.le_succ_of_le hm) q.out * (ratPoint F ρ * x))‖ ≤ b T e q

instance subsingleton_unipotentRationalCosets_zero :
    Subsingleton (UnipotentRationalCosets F 0) := by
  refine ⟨fun a b => Quotient.inductionOn₂ a b fun x y => ?_⟩
  have hxy : x = y := Units.ext (Matrix.ext fun i _ => Fin.elim0 i)
  rw [hxy]

variable [CompactSpace (AdeleQuotient F)] {V}
  {R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V} (hV : WhittakerDecayClass F r V R)
  (hψ : IsStandardAdditiveCharacter F ψ)

include hV hψ

omit [CompactSpace (AdeleQuotient F)] in
/-- **Level `0`.** `W_f(ρ x)` is bounded on `C` uniformly in rational `ρ`, by the band bound. -/
theorem levelMajorants_zero : LevelMajorants F V ψ 0 (Nat.zero_le r) := by
  refine ⟨0, fun f C hC => ?_⟩
  have hcont : Continuous fun x : Points F (r + 1) => (detNorm F (r + 1) x)⁻¹ :=
    (continuous_detNorm F (r + 1)).inv₀ fun x => (detNorm_pos F (r + 1) x).ne'
  obtain ⟨H₁, hH₁⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨H₂, hH₂⟩ := hC.exists_bound_of_continuousOn (continuous_detNorm F (r + 1)).continuousOn
  have hmax : 0 < max H₁ 1 := lt_max_of_lt_right one_pos
  obtain ⟨B, hB⟩ := hV.bounded f (max H₁ 1)⁻¹ H₂ (inv_pos.mpr hmax)
  refine ⟨max B 0, fun _ _ _ => max B 0, le_max_right _ _, fun T _ e _ =>
    ⟨fun _ => le_max_right _ _, Summable.of_finite, ?_, ?_⟩⟩
  · rw [tsum_eq_single (Quotient.mk _ 1 : UnipotentRationalCosets F 0)
      fun q hq => absurd (Subsingleton.elim q _) hq, pow_zero, mul_one]
  · intro ρ _ q x hx
    have hdet : detNorm F (r + 1) (padRational F (Nat.le_succ_of_le (Nat.zero_le r)) q.out *
        (ratPoint F ρ * x)) = detNorm F (r + 1) x := by
      rw [padRational_eq_ratPoint, detNorm_mul, detNorm_ratPoint, detNorm_mul, detNorm_ratPoint,
        one_mul, one_mul]
    refine (norm_whittaker_le_of_band F ψ hψ _ hB _ ?_ ?_).trans (le_max_left _ _)
    · rw [hdet]
      have h1 : (detNorm F (r + 1) x)⁻¹ ≤ max H₁ 1 :=
        ((Real.le_norm_self _).trans (hH₁ x hx)).trans (le_max_left _ _)
      exact (inv_le_comm₀ hmax (detNorm_pos F (r + 1) x)).mpr h1
    · rw [hdet]
      exact (Real.le_norm_self _).trans (hH₂ x hx)

/-- **Induction step.** Majorants at level `j < r` give majorants at level `j + 1`. -/
theorem levelMajorants_succ {j : ℕ} (hj : j < r) (hIH : LevelMajorants F V ψ j hj.le) :
    LevelMajorants F V ψ (j + 1) hj := by
  obtain ⟨k, hk⟩ := hIH
  set s : ℕ := (j + 1) * Module.finrank ℚ F + 1 with hs
  set N : ℕ := 2 * Module.finrank ℚ F * k + s with hN
  refine ⟨2 * N + 5 * k, fun f C hC => ?_⟩
  obtain ⟨c, hc0, hc⟩ := exists_lastRow_decay F hV ψ hψ hj N hC
  obtain ⟨L, hL, hfL⟩ := hV.level f
  obtain ⟨D₀, hD₀, hD⟩ := exists_support_denominator F hj ψ hψ (f : Points F (r + 1) → ℂ)
    (hV.rational f) L hL hfL hC
  choose A b hA0 hb using fun o => hk (wordFamily F (R := R) N f o) C hC
  set Z₀ : ℝ := ∑' v : EqualAnalytic.IntegralRows F (j + 1) 1, (rowSize F v.1 ^ s)⁻¹ with hZ₀
  have hZ₀0 : 0 ≤ Z₀ := tsum_nonneg fun v => inv_nonneg.mpr (pow_nonneg (rowSize_pos F _).le _)
  set SA : ℝ := ∑ o, A o with hSA
  have hSA0 : 0 ≤ SA := Finset.sum_nonneg fun o _ => hA0 o
  have hn1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 r
  refine ⟨Z₀ * c * SA * ((r + 1 : ℕ) : ℝ) ^ k * (D₀ : ℝ) ^ N * (D₀ : ℝ) ^ (2 * k),
    stepMajorant F r j b c N D₀, by positivity, ?_⟩
  intro T hT e he
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = D₀ * e ^ 2 := ⟨_, rfl⟩
  have hM0 : 0 < M := hM ▸ Nat.mul_pos hD₀ (pow_pos he 2)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM0
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hmaj : ∀ q, stepMajorant F r j b c N D₀ T e q =
      weightedFamily F (j + 1) N (stepFamily F r b c N M T e)
        (fun i => (M : F) * cosetRow F q i, cosetRest F q) := by
    intro q
    rw [stepMajorant, hM]
  have hTh : ∀ v : Fin (j + 1) → F, 1 ≤ stepHeight F r M T v := fun v =>
    one_le_mul_of_one_le_of_one_le hn1 (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hM1 (one_le_pow₀ (one_le_rowSize F v))) hT)
  have heh : ∀ v : Fin (j + 1) → F, 0 < rowDen F M v * e := fun v =>
    Nat.mul_pos (rowDen_pos F M v) he
  have hβ0 : ∀ (v : Fin (j + 1) → F) q', 0 ≤ stepFamily F r b c N M T e v q' := by
    intro v q'
    rw [stepFamily]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun o _ => (hb o _ (hTh v) _ (heh v)).1 q')
  have hβs : ∀ v : Fin (j + 1) → F, Summable (stepFamily F r b c N M T e v) := fun v =>
    (summable_sum fun o _ => (hb o _ (hTh v) _ (heh v)).2.1).mul_left
      ((M : ℝ) ^ N * c * T ^ (2 * N))
  set K : ℝ := (M : ℝ) ^ N * c * T ^ (2 * N) * SA * (((r + 1 : ℕ) : ℝ) * (M : ℝ) ^ 2 * T * e) ^ k
    with hK
  have hKb : ∀ v ∈ EqualAnalytic.IntegralRows F (j + 1) 1,
      ∑' q', stepFamily F r b c N M T e v q' ≤
        K * rowSize F v ^ (2 * Module.finrank ℚ F * k) := by
    intro v _
    have hrs := rowSize_pos F v
    have hsumm := fun o => (hb o _ (hTh v) _ (heh v)).2.1
    have hle := fun o => (hb o _ (hTh v) _ (heh v)).2.2.1
    have hTe : stepHeight F r M T v * ((rowDen F M v * e : ℕ) : ℝ) ≤
        ((r + 1 : ℕ) : ℝ) * (M : ℝ) ^ 2 * T * e * rowSize F v ^ (2 * Module.finrank ℚ F) := by
      have h1 := rowDen_le F hM0 v
      rw [stepHeight, Nat.cast_mul]
      calc ((r + 1 : ℕ) : ℝ) * ((M : ℝ) * rowSize F v ^ Module.finrank ℚ F * T) *
            ((rowDen F M v : ℝ) * e) =
            (((r + 1 : ℕ) : ℝ) * M * rowSize F v ^ Module.finrank ℚ F * T * e) *
              rowDen F M v := by ring
        _ ≤ (((r + 1 : ℕ) : ℝ) * M * rowSize F v ^ Module.finrank ℚ F * T * e) *
              (M * rowSize F v ^ Module.finrank ℚ F) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by ring
    have hTe0 : 0 ≤ stepHeight F r M T v * ((rowDen F M v * e : ℕ) : ℝ) :=
      mul_nonneg (zero_le_one.trans (hTh v)) (Nat.cast_nonneg _)
    have hexp : ∑' q', stepFamily F r b c N M T e v q' = (M : ℝ) ^ N * c * T ^ (2 * N) *
        ∑ o, ∑' q', b o (stepHeight F r M T v) (rowDen F M v * e) q' := by
      simp only [stepFamily]
      rw [tsum_mul_left, Summable.tsum_finsetSum fun o _ => hsumm o]
    rw [hexp]
    have hX0 : 0 ≤ (M : ℝ) ^ N * c * T ^ (2 * N) := by positivity
    calc (M : ℝ) ^ N * c * T ^ (2 * N) *
          ∑ o, ∑' q', b o (stepHeight F r M T v) (rowDen F M v * e) q' ≤
          (M : ℝ) ^ N * c * T ^ (2 * N) * ∑ o, A o *
            (stepHeight F r M T v * ((rowDen F M v * e : ℕ) : ℝ)) ^ k :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o _ => hle o) hX0
      _ = (M : ℝ) ^ N * c * T ^ (2 * N) *
            (SA * (stepHeight F r M T v * ((rowDen F M v * e : ℕ) : ℝ)) ^ k) := by
          rw [hSA, Finset.sum_mul]
      _ ≤ (M : ℝ) ^ N * c * T ^ (2 * N) * (SA * (((r + 1 : ℕ) : ℝ) * (M : ℝ) ^ 2 * T * e *
            rowSize F v ^ (2 * Module.finrank ℚ F)) ^ k) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hTe0 hTe k) hSA0) hX0
      _ = K * rowSize F v ^ (2 * Module.finrank ℚ F * k) := by
          rw [hK, mul_pow _ (rowSize F v ^ _), ← pow_mul]
          ring
  obtain ⟨hGs, hGt⟩ := summable_weightedFamily F (n := j + 1) (a := 2 * Module.finrank ℚ F * k)
    (s := s) (Nat.lt_succ_self _) hβ0 hβs hKb
  have hinj : Function.Injective fun q : UnipotentRationalCosets F (j + 1) =>
      ((fun i => (M : F) * cosetRow F q i), cosetRest F q) := by
    intro q₁ q₂ h12
    simp only [Prod.mk.injEq] at h12
    apply cosetRow_cosetRest_injective F
    simp only [Prod.mk.injEq]
    exact ⟨funext fun i => mul_left_cancel₀ hMF (congrFun h12.1 i), h12.2⟩
  have hfun : stepMajorant F r j b c N D₀ T e =
      weightedFamily F (j + 1) N (stepFamily F r b c N M T e) ∘
        fun q => ((fun i => (M : F) * cosetRow F q i), cosetRest F q) := funext hmaj
  have hsum' : Summable (stepMajorant F r j b c N D₀ T e) := by
    rw [hfun]
    exact hGs.comp_injective hinj
  refine ⟨fun q => by rw [hmaj]; exact weightedFamily_nonneg F hβ0 _, hsum', ?_, ?_⟩
  · -- the total mass
    have hD₀0 : (0 : ℝ) ≤ D₀ := Nat.cast_nonneg _
    have hA'0 : 0 ≤ Z₀ * c * SA * ((r + 1 : ℕ) : ℝ) ^ k * (D₀ : ℝ) ^ N * (D₀ : ℝ) ^ (2 * k) := by
      positivity
    calc ∑' q, stepMajorant F r j b c N D₀ T e q ≤
          ∑' p, weightedFamily F (j + 1) N (stepFamily F r b c N M T e) p := by
          rw [hfun]
          exact Summable.tsum_le_tsum_of_inj _ hinj
            (fun p _ => weightedFamily_nonneg F hβ0 p) (fun q => le_rfl)
            (hGs.comp_injective hinj) hGs
      _ ≤ K * Z₀ := hGt
      _ = (Z₀ * c * SA * ((r + 1 : ℕ) : ℝ) ^ k * (D₀ : ℝ) ^ N * (D₀ : ℝ) ^ (2 * k)) *
            (T ^ (2 * N + k) * (e : ℝ) ^ (2 * N + 5 * k)) := by
          rw [hK, hM, Nat.cast_mul, Nat.cast_pow]
          ring
      _ ≤ (Z₀ * c * SA * ((r + 1 : ℕ) : ℝ) ^ k * (D₀ : ℝ) ^ N * (D₀ : ℝ) ^ (2 * k)) *
            (T * e) ^ (2 * N + 5 * k) := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hT (by omega)) (by positivity)) hA'0
  · -- the pointwise bound
    intro ρ hρ q x hx
    rw [hmaj]
    by_cases hW : whittaker F r ψ (f : Points F (r + 1) → ℂ)
        (padRational F (by omega : j + 1 ≤ r + 1) q.out * (ratPoint F ρ * x)) = 0
    · rw [hW, norm_zero]
      exact weightedFamily_nonneg F hβ0 _
    have hint := hD e ρ (fun a b' => (hρ.1 a b').2) (fun a b' => (hρ.2 a b').2) x hx q.out hW
    rw [← hM] at hint
    have hv : (fun i => (M : F) * cosetRow F q i) ∈ EqualAnalytic.IntegralRows F (j + 1) 1 :=
      fun i => ⟨⟨(M : F) * cosetRow F q i, hint i⟩, by
        rw [map_one, one_mul]
        exact (RingOfIntegers.map_mk _ _).symm⟩
    have hv0 : (fun i => (M : F) * cosetRow F q i) ≠ 0 := by
      intro h0
      apply cosetRow_ne_zero F q
      funext i
      have h1 := congrFun h0 i
      simp only [Pi.zero_apply, mul_eq_zero, hMF, false_or] at h1
      exact h1
    have hγ : HeightLE F ((M : ℝ) * rowSize F (fun i => (M : F) * cosetRow F q i) ^
        Module.finrank ℚ F) (rowDen F M (fun i => (M : F) * cosetRow F q i)) (cosetGamma F q) := by
      have h1 : HeightLE F ((M : ℝ) * rowSize F (fun i => (M : F) * cosetRow F q i) ^
          Module.finrank ℚ F) (rowDen F M (fun i => (M : F) * cosetRow F q i))
          (rowGamma F fun i => (M : F) * cosetRow F q i / M) := heightLE_rowDen F hM0 hv hv0
      have h2 : (rowGamma F fun i => (M : F) * cosetRow F q i / M) = cosetGamma F q := by
        rw [← rowGamma_cosetRow F q]
        congr 1
        funext i
        exact mul_div_cancel_left₀ _ hMF
      rwa [h2] at h1
    have hMrs : (1 : ℝ) ≤ M * rowSize F (fun i => (M : F) * cosetRow F q i) ^
        Module.finrank ℚ F :=
      one_le_mul_of_one_le_of_one_le hM1 (one_le_pow₀ (one_le_rowSize F _))
    have hρ' := (hγ.pad (by omega : j + 1 ≤ r + 1) hMrs).mul hρ
    have hWo : ∀ o, ‖whittaker F r ψ ((wordFamily F (R := R) N f o : V) : Points F (r + 1) → ℂ)
        (padRational F (by omega : j + 1 ≤ r + 1) q.out * (ratPoint F ρ * x))‖ ≤
        b o (stepHeight F r M T (fun i => (M : F) * cosetRow F q i))
          (rowDen F M (fun i => (M : F) * cosetRow F q i) * e) (cosetRest F q) := by
      intro o
      rw [whittaker_padRational_coset F hj ψ hψ _ (hV.rational _) q,
        padRational_eq_ratPoint F _ (cosetGamma F q), ← mul_assoc (ratPoint F _),
        ← ratPoint_mul]
      exact (hb o _ (hTh _) _ (heh _)).2.2.2 _ hρ' (cosetRest F q) x hx
    have hA : rowSize F (cosetRow F q) ^ N * ‖whittaker F r ψ (f : Points F (r + 1) → ℂ)
        (padRational F (by omega : j + 1 ≤ r + 1) q.out * (ratPoint F ρ * x))‖ ≤
        c * T ^ (2 * N) * ∑ o, ‖whittaker F r ψ
          ((wordFamily F (R := R) N f o : V) : Points F (r + 1) → ℂ)
          (padRational F (by omega : j + 1 ≤ r + 1) q.out * (ratPoint F ρ * x))‖ :=
      hc f T hT e ρ hρ x hx q.out
    have hsum := Finset.sum_le_sum fun o (_ : o ∈ Finset.univ) => hWo o
    have hvs : rowSize F (fun i => (M : F) * cosetRow F q i) ^ N ≤
        (M : ℝ) ^ N * rowSize F (cosetRow F q) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (rowSize_pos F _).le (rowSize_natCast_mul_le F hM0 _) N
    have key : ∀ {Wf So Sb : ℝ}, 0 ≤ Wf → rowSize F (cosetRow F q) ^ N * Wf ≤
        c * T ^ (2 * N) * So → So ≤ Sb →
        rowSize F (fun i => (M : F) * cosetRow F q i) ^ N * Wf ≤
          (M : ℝ) ^ N * c * T ^ (2 * N) * Sb := by
      intro Wf So Sb hWf0 h1 h2
      calc rowSize F (fun i => (M : F) * cosetRow F q i) ^ N * Wf ≤
            (M : ℝ) ^ N * rowSize F (cosetRow F q) ^ N * Wf :=
            mul_le_mul_of_nonneg_right hvs hWf0
        _ = (M : ℝ) ^ N * (rowSize F (cosetRow F q) ^ N * Wf) := by ring
        _ ≤ (M : ℝ) ^ N * (c * T ^ (2 * N) * So) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (M : ℝ) ^ N * (c * T ^ (2 * N) * Sb) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity))
              (by positivity)
        _ = (M : ℝ) ^ N * c * T ^ (2 * N) * Sb := by ring
    rw [weightedFamily]
    dsimp only
    rw [ite_eq_left hv, stepFamily, le_inv_mul_iff₀ (pow_pos (rowSize_pos F _) N)]
    exact key (norm_nonneg _) hA hsum

/-- Majorants at every level `m ≤ r`. -/
theorem levelMajorants : ∀ (m : ℕ) (hm : m ≤ r), LevelMajorants F V ψ m hm := by
  intro m
  induction m with
  | zero => intro hm; exact levelMajorants_zero F ψ hV hψ
  | succ j ih => intro hm; exact levelMajorants_succ F ψ hV hψ hm (ih (Nat.le_of_succ_le hm))

/-- Every function of a decay class has locally uniform summable majorants. -/
theorem hasWhittakerMajorants_of_decayClass (f : V) :
    HasWhittakerMajorants F r ψ (f : Points F (r + 1) → ℂ) := by
  intro j hj C hC
  obtain ⟨k, hk⟩ := levelMajorants F ψ hV hψ j hj
  obtain ⟨A, b, -, hb⟩ := hk f C hC
  obtain ⟨-, hs, -, hbd⟩ := hb 1 le_rfl 1 one_pos
  refine ⟨b 1 1, hs, fun q x hx => ?_⟩
  have h := hbd 1 (HeightLE.one 1) q x hx
  rwa [ratPoint_one, one_mul] at h

omit hV hψ in
/-- **Half (S).** -/
theorem whittakerMajorantsStatement_proof : WhittakerMajorantsStatement F :=
  fun _ _ _ hV ψ hψ f => hasWhittakerMajorants_of_decayClass F ψ hV hψ f

end Induction

end Langlands.Global.RankinSelbergGlobal.Unfolding
