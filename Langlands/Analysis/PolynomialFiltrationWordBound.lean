import Langlands.Analysis.GeometricApproximationBound

/-! # Finite-word bounds from polynomial layers and commuting approximants -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Analysis.PolynomialFiltrationWordBound

universe uU uE uA

section Iteration

variable {α U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
variable [DecidableEq α]

private def wordSupport (Γ : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | m + 1 => wordSupport Γ m ∪ Γ.biUnion fun X => (wordSupport Γ m).image (· ++ [X])

private theorem nil_mem_wordSupport (Γ : Finset α) (m : ℕ) : [] ∈ wordSupport Γ m := by
  induction m with
  | zero => simp [wordSupport]
  | succ m ih => exact Finset.mem_union_left _ ih

/-- Apply the indicated operators from the last letter of the word to the first. -/
def applyWord (D : α → Module.End ℂ U) (Xs : List α) (v : U) : U :=
  Xs.foldr (fun X w => D X w) v

private theorem wordSums_le (D : α → Module.End ℂ U) (Γ : Finset α) (m : ℕ) (v : U) :
    (∑ Xs ∈ wordSupport Γ m, ‖applyWord D Xs v‖) +
      ∑ X ∈ Γ, ∑ Xs ∈ wordSupport Γ m, ‖applyWord D Xs (D X v)‖ ≤
      (1 + (Γ.card : ℝ)) * ∑ Xs ∈ wordSupport Γ (m + 1), ‖applyWord D Xs v‖ := by
  let S := wordSupport Γ m
  let T := wordSupport Γ (m + 1)
  let Q := ∑ Xs ∈ T, ‖applyWord D Xs v‖
  have hS : S ⊆ T := Finset.subset_union_left
  have hv : (∑ Xs ∈ S, ‖applyWord D Xs v‖) ≤ Q :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => norm_nonneg _)
  have hX (X : α) (hX : X ∈ Γ) : (∑ Xs ∈ S, ‖applyWord D Xs (D X v)‖) ≤ Q := by
    let R := S.image (· ++ [X])
    have hR : R ⊆ T := by
      intro Xs hXs
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨X, hX, hXs⟩
    have he : (∑ Xs ∈ S, ‖applyWord D Xs (D X v)‖) = ∑ Xs ∈ R, ‖applyWord D Xs v‖ := by
      unfold R
      rw [Finset.sum_image (fun _ _ _ _ h => List.append_cancel_right h)]
      simp only [applyWord, List.foldr_append, List.foldr_cons, List.foldr_nil]
    rw [he]
    exact Finset.sum_le_sum_of_subset_of_nonneg hR (fun _ _ _ => norm_nonneg _)
  calc
    _ ≤ Q + ∑ _X ∈ Γ, Q := add_le_add hv (Finset.sum_le_sum hX)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; change _ = (1 + (Γ.card : ℝ)) * Q; ring

private theorem errorPower_le (D : α → Module.End ℂ U) (Γ : Finset α)
    (A : Module.End ℂ U) {δ : ℝ} (hδ : 0 ≤ δ)
    (hComm : ∀ X ∈ Γ, ∀ v, A (D X v) = D X (A v))
    (hError : ∀ v, ‖A v - v‖ ≤ δ * (‖v‖ + ∑ X ∈ Γ, ‖D X v‖)) :
    ∀ m v, ‖((1 - A) ^ m) v‖ ≤ (δ * (1 + (Γ.card : ℝ))) ^ m *
      ∑ Xs ∈ wordSupport Γ m, ‖applyWord D Xs v‖ := by
  let E := 1 - A
  let B := δ * (1 + (Γ.card : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE (v : U) : E v = v - A v := rfl
  have hEComm (X : α) (hX : X ∈ Γ) : Commute (D X) E := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, Module.End.mul_apply, hE, map_sub, hE, hComm X hX]
  intro m
  induction m with
  | zero => intro v; simp [wordSupport, applyWord, Module.End.one_apply]
  | succ m ih =>
    intro v
    let p (l : ℕ) (u : U) := ∑ Xs ∈ wordSupport Γ l, ‖applyWord D Xs u‖
    have h₁ (u : U) : ‖(E ^ m) u‖ ≤ B ^ m * p m u := ih u
    have h₂ (X : α) (hX : X ∈ Γ) : ‖D X ((E ^ m) v)‖ ≤ B ^ m * p m (D X v) := by
      have he := congrArg (fun f : Module.End ℂ U => f v) ((hEComm X hX).pow_right m).eq
      change D X ((E ^ m) v) = (E ^ m) (D X v) at he
      rw [he]
      exact h₁ (D X v)
    change ‖(E ^ (m + 1)) v‖ ≤ B ^ (m + 1) * p (m + 1) v
    rw [pow_succ' E, Module.End.mul_apply, hE, norm_sub_rev]
    calc
      _ ≤ δ * (‖(E ^ m) v‖ + ∑ X ∈ Γ, ‖D X ((E ^ m) v)‖) := hError _
      _ ≤ δ * (B ^ m * p m v + ∑ X ∈ Γ, B ^ m * p m (D X v)) :=
        mul_le_mul_of_nonneg_left (add_le_add (h₁ _) (Finset.sum_le_sum h₂)) hδ
      _ = (δ * B ^ m) * (p m v + ∑ X ∈ Γ, p m (D X v)) := by rw [← Finset.mul_sum]; ring
      _ ≤ (δ * B ^ m) * ((1 + (Γ.card : ℝ)) * p (m + 1) v) :=
        mul_le_mul_of_nonneg_left (wordSums_le D Γ m v) (mul_nonneg hδ (pow_nonneg hB _))
      _ = _ := by rw [pow_succ B]; dsimp only [B]; ring

private theorem sub_errorPower_mem (A : Module.End ℂ U) (W : Submodule ℂ U)
    (hA : ∀ v, A v ∈ W) (m : ℕ) (v : U) : v - ((1 - A) ^ m) v ∈ W := by
  let E := 1 - A
  have hE (w : U) : E w = w - A w := rfl
  change v - (E ^ m) v ∈ W
  induction m with
  | zero => simp [Module.End.one_apply]
  | succ m ih =>
    rw [pow_succ' E, Module.End.mul_apply, hE]
    rw [show v - ((E ^ m) v - A ((E ^ m) v)) = (v - (E ^ m) v) + A ((E ^ m) v) by abel]
    exact W.add_mem ih (hA _)

private theorem sub_errorPower_preserves (A : Module.End ℂ U) (W : Submodule ℂ U)
    (hA : ∀ v ∈ W, A v ∈ W) (m : ℕ) {v : U} (hv : v ∈ W) : v - ((1 - A) ^ m) v ∈ W := by
  apply W.sub_mem hv
  let E := 1 - A
  have hE (w : U) : E w = w - A w := rfl
  change (E ^ m) v ∈ W
  induction m with
  | zero => exact hv
  | succ m ih =>
    rw [pow_succ' E, Module.End.mul_apply, hE]
    exact W.sub_mem ih (hA _ ih)

end Iteration

/-- Degree bounds and polynomial approximations commuting with a finite family of directions
imply a single estimate by the original norm of finitely many derivative words. -/
def PolynomialFiltrationWordBoundStatement : Prop :=
  ∀ (U : Type uU) [NormedAddCommGroup U] [NormedSpace ℂ U]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (W : ℕ → Submodule ℂ U) (T : U →ₗ[ℂ] E)
    (α : Type uA) [DecidableEq α] (Γ : Finset α) (D : α → Module.End ℂ U)
    (C B : ℝ) (d : ℕ), 0 ≤ C → 0 ≤ B → Monotone W → (∀ v : U, ∃ N, v ∈ W N) →
    (∀ N v, v ∈ W N → ‖T v‖ ≤ C * (1 + (N : ℝ)) ^ d * ‖v‖) →
    (∀ t : ℕ, 0 < t → ∃ A : Module.End ℂ U,
      (∀ v, A v ∈ W (t ^ 4)) ∧ (∀ N v, v ∈ W N → A v ∈ W N) ∧
      (∀ X ∈ Γ, ∀ v, A (D X v) = D X (A v)) ∧
      ∀ v, ‖A v - v‖ ≤ B / (t : ℝ) * (‖v‖ + ∑ X ∈ Γ, ‖D X v‖)) →
    ∃ (S : Finset (List α)) (F : ℝ), 0 ≤ F ∧
      ∀ v, ‖T v‖ ≤ F * ∑ Xs ∈ S, ‖applyWord D Xs v‖

set_option maxHeartbeats 1100000 in
theorem polynomialFiltrationWordBound : PolynomialFiltrationWordBoundStatement.{uU, uE, uA} := by
  intro U _ _ E _ _ W₀ T α _ Γ D C B d hC hB hW hCover hDegree hApprox
  let t (j : ℕ) : ℕ := 2 ^ j
  have ht (j : ℕ) : 0 < t j := by dsimp [t]; positivity
  choose A hA using fun j : ℕ => hApprox (t j) (ht j)
  let W (j : ℕ) : Submodule ℂ U := W₀ ((t j) ^ 4)
  let m := 4 * d + 1
  let a := ((2 : ℝ) ^ m)⁻¹
  let b := (2 : ℝ) ^ (4 * d)
  let H := (B * (1 + (Γ.card : ℝ))) ^ m
  let S := wordSupport Γ m
  let p (v : U) := H * ∑ Xs ∈ S, ‖applyWord D Xs v‖
  let vApprox (j : ℕ) (v : U) := v - ((1 - A j) ^ m) v
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hp (v : U) : 0 ≤ p v := mul_nonneg hH (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 1 ≤ b := one_le_pow₀ (by norm_num)
  have hab : a * b < 1 := by
    dsimp only [a]
    rw [← div_eq_inv_mul]
    apply (div_lt_one (by positivity)).mpr
    exact pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self _)
  have hmono : Monotone W := fun _ _ hij =>
    hW (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) hij) _)
  have hcover (v : U) : ∃ j, v ∈ W j := by
    obtain ⟨N, hN⟩ := hCover v
    have hNle : N ≤ 2 ^ N := Nat.lt_two_pow_self.le
    exact ⟨N, hW (hNle.trans (Nat.le_self_pow (by decide) _)) hN⟩
  have hLayer (j : ℕ) (v : U) (hv : v ∈ W j) : ‖T v‖ ≤ (C * (2 : ℝ) ^ d) * b ^ j * ‖v‖ := by
    let s := (2 : ℝ) ^ j
    have hs : 1 ≤ s := one_le_pow₀ (by norm_num)
    have hcast : ((t j : ℕ) : ℝ) = s := by simp [t, s]
    have hscale : 1 + s ^ 4 ≤ 2 * s ^ 4 := by linarith [one_le_pow₀ hs (n := 4)]
    have h := hDegree ((t j) ^ 4) v hv
    change ‖T v‖ ≤ C * (1 + (((t j) ^ 4 : ℕ) : ℝ)) ^ d * ‖v‖ at h
    rw [Nat.cast_pow, hcast] at h
    calc
      _ ≤ C * (1 + s ^ 4) ^ d * ‖v‖ := h
      _ ≤ C * (2 * s ^ 4) ^ d * ‖v‖ := by gcongr
      _ = _ := by
        rw [mul_pow (2 : ℝ), ← pow_mul s]
        dsimp only [s, b]
        rw [← pow_mul, Nat.mul_comm j (4 * d), pow_mul]
        ring
  have hP (j : ℕ) (v : U) : vApprox j v ∈ W j := sub_errorPower_mem (A j) (W j) (hA j).1 m v
  have hPres (j l : ℕ) (v : U) (hv : v ∈ W l) : vApprox j v ∈ W l :=
    sub_errorPower_preserves (A j) (W l) ((hA j).2.1 ((t l) ^ 4)) m hv
  have hError (j : ℕ) (v : U) : ‖vApprox j v - v‖ ≤ a ^ j * p v := by
    have h := errorPower_le D Γ (A j) (div_nonneg hB (Nat.cast_nonneg (t j)))
      (hA j).2.2.1 (hA j).2.2.2 m v
    change ‖v - ((1 - A j) ^ m) v - v‖ ≤ _
    rw [show v - ((1 - A j) ^ m) v - v = -(((1 - A j) ^ m) v) by abel, norm_neg]
    refine h.trans_eq ?_
    have hscale : (B / (t j : ℝ) * (1 + (Γ.card : ℝ))) ^ m = a ^ j * H := by
      have he : B / (t j : ℝ) * (1 + (Γ.card : ℝ)) = (B * (1 + (Γ.card : ℝ))) / ((2 : ℝ) ^ j) := by
        simp only [t, Nat.cast_pow, Nat.cast_ofNat]
        ring
      rw [he, div_pow, ← pow_mul, Nat.mul_comm j m, pow_mul, div_eq_mul_inv]
      simp only [a, H, inv_pow, mul_comm]
    rw [hscale]
    change (a ^ j * H) * (∑ Xs ∈ S, ‖applyWord D Xs v‖) = a ^ j * p v
    rw [mul_assoc]
  obtain ⟨F, hF, hBound⟩ := Langlands.Analysis.geometricApproximationBound U E W T vApprox p
    (C * (2 : ℝ) ^ d) a b hmono hcover hp (by positivity) ha hb hab hLayer hP hPres hError
  refine ⟨S, F * (1 + H), by positivity, fun v => ?_⟩
  let J := ∑ Xs ∈ S, ‖applyWord D Xs v‖
  have hv : ‖v‖ ≤ J := by
    change ‖applyWord D [] v‖ ≤ _
    exact Finset.single_le_sum (f := fun Xs => ‖applyWord D Xs v‖)
      (fun _ _ => norm_nonneg _) (nil_mem_wordSupport Γ m)
  calc
    _ ≤ F * (‖v‖ + H * J) := hBound v
    _ ≤ F * (J + H * J) := mul_le_mul_of_nonneg_left (add_le_add hv le_rfl) hF
    _ = _ := by ring

end Langlands.Analysis.PolynomialFiltrationWordBound
