import Langlands.LinearAlgebra.ArthurCombinatoricsSigma

/-!
# The support of `σ_{P_1}^{P_2}`

Arthur 2005, Lemma 8.3, read off from Arthur 1978, Lemma 6.1 (`sigma_eq`) and the argument of
Arthur 1978, Corollary 6.2.

* `sigma_eq_zero_or_one`: `σ` takes only the values `0` and `1`;
* `sigma_support_bound`: if `σ_{P_1}^{P_2}(H₁₂ + H₂) = 1` with `H₁₂ ∈ 𝔞_{P_1}^{P_2}` and
  `H₂ ∈ 𝔞_{P_2}^G`, then `τ_{P_1}^{P_2}(H₁₂) = 1` and the coordinates of `H₂` in the coroot basis
  are bounded by a constant multiple of those of `H₁₂`;
* `sigmaSupportStatement`.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.ArthurCombinatorics

open Finset

variable {ι M N : Type*} [DecidableEq ι] [Finite ι] [AddCommGroup M] [Module ℝ M]
  [AddCommGroup N] [Module ℝ N] {P : RootPairing ι ℝ M N} [P.IsRootSystem]
  [P.IsCrystallographic] (b : P.Base)

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] in
/-- The projection `H ↦ H_P` is the identity on `𝔞_P^G`. -/
theorem levelProjection_eq_self {Θ : Finset ι} {Z : N} (hZ : Z ∈ rootAnnihilator P Θ) :
    levelProjection P Θ Z = Z := by
  have h0 : ∀ j, weightCoordinate P Θ j Z = 0 := fun j =>
    weightCoordinate_eq_zero_of_mem_rootAnnihilator j hZ
  rw [levelProjection_apply]
  simp [h0]

omit [P.IsCrystallographic] in
/-- For `Θ ⊆ S ⊆ b.support` and `k ∈ S \ Θ`, `ϖ^S_k` vanishes on `𝔞_0^P = corootSpan P Θ`. -/
theorem weightCoordinate_eq_zero_of_mem_corootSpan {Θ S : Finset ι} (hΘS : Θ ⊆ S)
    (hS : S ⊆ b.support) {k : ι} (hk : k ∈ S) (hkΘ : k ∉ Θ) {Z : N}
    (hZ : Z ∈ corootSpan P Θ) : weightCoordinate P S k Z = 0 := by
  have hle : corootSpan P Θ ≤ LinearMap.ker (weightCoordinate P S k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, hj, rfl⟩
    show weightCoordinate P S k (P.coroot j) = 0
    exact (weightCoordinate_coroot b hS hk (hΘS hj)).trans
      (ite_eq_right fun e : k = j => hkΘ (e ▸ hj))
  exact LinearMap.mem_ker.mp (hle hZ)

omit [P.IsCrystallographic] in
/-- The coordinates in the coroot basis of `b` are the weights `ϖ_j = weightCoordinate P b.support j`. -/
theorem toCoweightBasis_repr_eq (Y : N) (j : b.support) :
    b.toCoweightBasis.repr Y j = weightCoordinate P b.support j Y := by
  have h : b.toCoweightBasis.coord j = weightCoordinate P b.support j := by
    refine b.toCoweightBasis.ext fun l => ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, RootPairing.Base.toCoweightBasis_apply,
      weightCoordinate_coroot b subset_rfl j.2 l.2, Finsupp.single_apply]
    by_cases h : l = j
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right fun e => h (Subtype.ext e.symm)]
  rw [← Module.Basis.coord_apply, h]

variable {b}

/-- Arthur 2005, Lemma 8.3 (a): `σ` takes only the values `0` and `1`. -/
theorem sigma_eq_zero_or_one {S Θ₁ Θ₂ : Finset ι} (h12 : Θ₁ ⊆ Θ₂) (h2S : Θ₂ ⊆ S)
    (hS : S ⊆ b.support) (H : N) : sigma P S Θ₁ Θ₂ H = 0 ∨ sigma P S Θ₁ Θ₂ H = 1 := by
  rw [sigma_eq h12 h2S hS H]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Arthur 2005, Lemma 8.3 (b), with an explicit constant. -/
theorem sigma_support_bound {Θ₁ Θ₂ : Finset ι} (h12 : Θ₁ ⊆ Θ₂) (h2 : Θ₂ ⊆ b.support) :
    ∃ c : ℝ, ∀ H₁₂ H₂ : N, H₁₂ ∈ rootAnnihilator P Θ₁ ⊓ corootSpan P Θ₂ →
      H₂ ∈ rootAnnihilator P Θ₂ → sigma P b.support Θ₁ Θ₂ (H₁₂ + H₂) = 1 →
        tau P Θ₁ Θ₂ H₁₂ = 1 ∧
          ∑ i, |b.toCoweightBasis.repr H₂ i| ≤ c * ∑ i, |b.toCoweightBasis.repr H₁₂ i| := by
  classical
  set S := b.support with hSdef
  set A := cartanBlock P S with hAdef
  set W := (cartanBlock P S)⁻¹ with hWdef
  set Ka : ℝ := ∑ l : S, ∑ j : S, |A l j| with hKadef
  set Kw : ℝ := ∑ i : S, ∑ l : S, W i l with hKwdef
  have hW : ∀ i l, 0 ≤ W i l := cartanBlock_inv_nonneg' b subset_rfl
  have hKw : 0 ≤ Kw := sum_nonneg fun i _ => sum_nonneg fun l _ => hW i l
  have hKa : 0 ≤ Ka := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(S.card : ℝ) * Kw * (1 + 2 * Kw) * Ka, fun H₁₂ H₂ h12m h2m hσ => ?_⟩
  obtain ⟨h12a, h12c⟩ := Submodule.mem_inf.mp h12m
  set n : ℝ := ∑ j, |b.toCoweightBasis.repr H₁₂ j| with hndef
  have hn : 0 ≤ n := sum_nonneg fun _ _ => abs_nonneg _
  have h2a : H₂ ∈ rootAnnihilator P Θ₁ := rootAnnihilator_anti h12 h2m
  have hHa : H₁₂ + H₂ ∈ rootAnnihilator P Θ₁ := add_mem h12a h2a
  rw [sigma_eq h12 h2 subset_rfl, levelProjection_eq_self hHa] at hσ
  have hc : (∀ i ∈ Θ₂ \ Θ₁, 0 < P.root' i (H₁₂ + H₂)) ∧
      (∀ i ∈ S \ Θ₂, P.root' i (H₁₂ + H₂) ≤ 0) ∧
      (∀ i ∈ S \ Θ₂, 0 < weightCoordinate P S i (H₁₂ + H₂)) := by
    by_contra hc
    rw [ite_eq_right hc] at hσ
    exact zero_ne_one hσ
  obtain ⟨hi, hii, hiii⟩ := hc
  have hα2 : ∀ l ∈ Θ₂, P.root' l H₂ = 0 := fun l hl =>
    root'_eq_zero_of_mem_rootAnnihilator h2m hl
  refine ⟨?_, ?_⟩
  · unfold tau
    rw [levelProjection_eq_self h12a, ite_eq_left]
    intro i hi'
    have := hi i hi'
    rwa [map_add, hα2 i (mem_sdiff.mp hi').1, add_zero] at this
  -- the roots in coroot coordinates
  have hroot : ∀ l : S, P.root' l H₁₂ = ∑ j : S, b.toCoweightBasis.repr H₁₂ j * A l j := by
    intro l
    conv_lhs => rw [← b.toCoweightBasis.sum_repr H₁₂]
    rw [map_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [map_smul, RootPairing.Base.toCoweightBasis_apply, smul_eq_mul, hAdef, cartanBlock_apply]
  set V : ℝ := Ka * n with hVdef
  have hV : 0 ≤ V := mul_nonneg hKa hn
  have hv : ∀ l : S, |P.root' l H₁₂| ≤ V := by
    intro l
    rw [hroot l]
    calc |∑ j : S, b.toCoweightBasis.repr H₁₂ j * A l j|
        ≤ ∑ j : S, |b.toCoweightBasis.repr H₁₂ j * A l j| := abs_sum_le_sum_abs _ _
      _ = ∑ j : S, |A l j| * |b.toCoweightBasis.repr H₁₂ j| :=
          sum_congr rfl fun j _ => by rw [abs_mul, mul_comm]
      _ ≤ ∑ j : S, |A l j| * n :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
            (single_le_sum (f := fun j => |b.toCoweightBasis.repr H₁₂ j|)
              (fun _ _ => abs_nonneg _) (mem_univ j)) (abs_nonneg _)
      _ = (∑ j : S, |A l j|) * n := by rw [sum_mul]
      _ ≤ Ka * n := mul_le_mul_of_nonneg_right
          (single_le_sum (f := fun l => ∑ j : S, |A l j|)
            (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ l)) hn
  have hrow : ∀ i : S, ∑ l : S, W i l ≤ Kw := fun i =>
    single_le_sum (f := fun i => ∑ l : S, W i l) (fun i _ => sum_nonneg fun l _ => hW i l)
      (mem_univ i)
  have hwH : ∀ (i : S) (Y : N), weightCoordinate P S i Y = ∑ l : S, W i l * P.root' l Y :=
    fun i Y => weightCoordinate_apply i.2 Y
  -- `α_l(H₂) ≤ |α_l(H₁₂)|`
  have hale : ∀ l : S, P.root' l H₂ ≤ |P.root' l H₁₂| := by
    intro l
    by_cases hl : (l : ι) ∈ Θ₂
    · rw [hα2 l hl]; exact abs_nonneg _
    · have := hii l (mem_sdiff.mpr ⟨l.2, hl⟩)
      rw [map_add] at this
      linarith [neg_le_abs (P.root' l H₁₂)]
  have hKwV : 0 ≤ Kw * V := mul_nonneg hKw hV
  -- `|α_i(H₂)|` is bounded
  have habs : ∀ i : S, |P.root' i H₂| ≤ (1 + 2 * Kw) * V := by
    intro i
    by_cases hi2 : (i : ι) ∈ Θ₂
    · rw [hα2 i hi2, abs_zero]
      nlinarith
    · have hpos := hiii i (mem_sdiff.mpr ⟨i.2, hi2⟩)
      have h12z : weightCoordinate P S i H₁₂ = 0 :=
        weightCoordinate_eq_zero_of_mem_corootSpan b h2 subset_rfl i.2 hi2 h12c
      rw [map_add, h12z, zero_add, hwH] at hpos
      have hD : W i i * (|P.root' i H₁₂| - P.root' i H₂) ≤
          ∑ l : S, W i l * (|P.root' l H₁₂| - P.root' l H₂) :=
        single_le_sum (f := fun l => W i l * (|P.root' l H₁₂| - P.root' l H₂))
          (fun l _ => mul_nonneg (hW i l) (sub_nonneg.mpr (hale l))) (mem_univ i)
      have hsplit : ∑ l : S, W i l * (|P.root' l H₁₂| - P.root' l H₂) =
          ∑ l : S, W i l * |P.root' l H₁₂| - ∑ l : S, W i l * P.root' l H₂ := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun l _ => mul_sub _ _ _
      have hWv : ∑ l : S, W i l * |P.root' l H₁₂| ≤ Kw * V :=
        calc ∑ l : S, W i l * |P.root' l H₁₂| ≤ ∑ l : S, W i l * V :=
              sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hv l) (hW i l)
          _ = (∑ l : S, W i l) * V := by rw [sum_mul]
          _ ≤ Kw * V := mul_le_mul_of_nonneg_right (hrow i) hV
      have hWii : 1 / 2 ≤ W i i := half_le_cartanBlock_inv_self b subset_rfl i
      have hd0 : 0 ≤ |P.root' i H₁₂| - P.root' i H₂ := sub_nonneg.mpr (hale i)
      have hhalf : (|P.root' i H₁₂| - P.root' i H₂) / 2 ≤
          W i i * (|P.root' i H₁₂| - P.root' i H₂) := by nlinarith
      have hvi := hv i
      have habs0 := abs_nonneg (P.root' i H₁₂)
      rw [abs_le]
      constructor <;> nlinarith
  have hcoord : ∀ j : S, |b.toCoweightBasis.repr H₂ j| ≤ Kw * ((1 + 2 * Kw) * V) := by
    intro j
    rw [toCoweightBasis_repr_eq, hwH]
    calc |∑ l : S, W j l * P.root' l H₂| ≤ ∑ l : S, |W j l * P.root' l H₂| :=
          abs_sum_le_sum_abs _ _
      _ = ∑ l : S, W j l * |P.root' l H₂| :=
          sum_congr rfl fun l _ => by rw [abs_mul, abs_of_nonneg (hW j l)]
      _ ≤ ∑ l : S, W j l * ((1 + 2 * Kw) * V) :=
          sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (habs l) (hW j l)
      _ = (∑ l : S, W j l) * ((1 + 2 * Kw) * V) := by rw [sum_mul]
      _ ≤ Kw * ((1 + 2 * Kw) * V) :=
          mul_le_mul_of_nonneg_right (hrow j) (mul_nonneg (by linarith) hV)
  calc ∑ j : S, |b.toCoweightBasis.repr H₂ j| ≤ ∑ _j : S, Kw * ((1 + 2 * Kw) * V) :=
        sum_le_sum fun j _ => hcoord j
    _ = (S.card : ℝ) * Kw * (1 + 2 * Kw) * Ka * n := by
        rw [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul, hVdef]
        ring

/-- **Arthur 2005, Lemma 8.3.** -/
theorem sigmaSupportStatement : SigmaSupportStatement.{u} := by
  intro ι M N _ _ _ _ _ _ P _ _ b Θ₁ Θ₂ h12 h2
  exact ⟨fun H => sigma_eq_zero_or_one h12 h2 subset_rfl H, sigma_support_bound h12 h2⟩

end Langlands.ArthurCombinatorics
