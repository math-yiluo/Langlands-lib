import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerSupport

/-! # Polynomial decay in the last row

For `j < r` and a compact set `C`, the Whittaker term `W_f(diag(γ, I) ρ x)` decays like
`(1 + ‖ξ‖)^(-N)` in the last row `ξ` of `γ ∈ GL_(j+1)(F)`, at the price of the factor `T^(2N)`
in the height `T` of `ρ` and of finitely many other functions of the decay class: the word
composites of length `N` of the derivatives along the matrix units. The constant does not depend
on `f`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Real
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints

local instance decaySchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance decaySchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

open scoped Classical

variable {r : ℕ} {V : Submodule ℂ (Points F (r + 1) → ℂ)}
  {R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V}

/-- The function `f` together with its word composites of length `N`: `none ↦ f` and
`some l ↦ R(D_(l 0)) ∘ ⋯ ∘ R(D_(l (N-1))) f`. -/
def wordFamily (N : ℕ) (f : V) : Option (Fin N → EntryIndex F (r + 1)) → V
  | none => f
  | some l => entryWord F (R := R) N l f

variable [CompactSpace (AdeleQuotient F)] (hV : WhittakerDecayClass F r V R)
  (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)

include hV hψ

/-- **Last-row decay.** For `j < r`, `N` and a compact set `C` there is `c ≥ 0` such that for
every `f` in the class, every rational `ρ` of height at most `(T, e)` with `T ≥ 1`, every
`x ∈ C` and every `γ ∈ GL_(j+1)(F)` with last row `ξ`,
`(1 + ‖ξ‖)^N ‖W_f(diag(γ, I) ρ x)‖ ≤ c T^(2N) Σ_o ‖W_(f_o)(diag(γ, I) ρ x)‖`,
where `f_o` runs over `f` and its word composites of length `N`. -/
theorem exists_lastRow_decay {j : ℕ} (hj : j < r) (N : ℕ) {C : Set (Points F (r + 1))}
    (hC : IsCompact C) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (f : V) (T : ℝ), 1 ≤ T → ∀ (e : ℕ) (ρ : RationalGL F (r + 1)),
      HeightLE F T e ρ → ∀ x ∈ C, ∀ g0 : RationalGL F (j + 1),
        (1 + ‖EqualAnalytic.rowEmbedding F (j + 1)
            ((g0 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j))‖) ^ N *
          ‖whittaker F r ψ (f : Points F (r + 1) → ℂ)
            (padRational F (by omega : j + 1 ≤ r + 1) g0 * (ratPoint F ρ * x))‖ ≤
        c * T ^ (2 * N) * ∑ o, ‖whittaker F r ψ
            ((wordFamily F (R := R) N f o : V) : Points F (r + 1) → ℂ)
            (padRational F (by omega : j + 1 ≤ r + 1) g0 * (ratPoint F ρ * x))‖ := by
  obtain ⟨β, hβ0, hβ⟩ := EqualAnalytic.exists_eq_standardCharacter_mul F ψ hψ
  obtain ⟨K₀, hK₀, hK⟩ := exists_norm_le_sum_colFrequency F hβ0
  obtain ⟨B, hB0, hB⟩ := exists_archCoord_bound (F := F) hC
  set Idx := Fin (j + 1) × Module.Free.ChooseBasisIndex ℤ (𝓞 F) with hIdx
  set ω₀ : ℝ := ∑ κ, ‖mixedEmbedding.latticeBasis F κ‖ with hω₀
  have hω₀0 : 0 ≤ ω₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set n₁ : ℝ := ((r + 1 : ℕ) : ℝ) with hn₁
  have hn₁0 : 0 ≤ n₁ := Nat.cast_nonneg _
  set c₆ : ℝ := coordConst F * (n₁ * (n₁ * (n₁ * B * ω₀) * (n₁ * B))) with hc₆
  have hc₆0 : 0 ≤ c₆ := mul_nonneg (coordConst_nonneg F) (by positivity)
  set P : ℝ := (1 + K₀) ^ N * (Fintype.card (Option Idx) : ℝ) ^ N with hP
  have hP0 : 0 ≤ P := by positivity
  set Q : ℝ := (Fintype.card Idx : ℝ) * c₆ ^ N with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨P * (1 + Q), by positivity, ?_⟩
  intro f T hT e ρ hρ x hx g0
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  set g := padRational F (by omega : j + 1 ≤ r + 1) g0 * (ratPoint F ρ * x) with hg
  set Wf := ‖whittaker F r ψ (f : Points F (r + 1) → ℂ) g‖ with hWf
  set S := ∑ l : Fin N → EntryIndex F (r + 1),
    ‖whittaker F r ψ ((entryWord F (R := R) N l f : V) : Points F (r + 1) → ℂ) g‖ with hS
  have hWf0 : 0 ≤ Wf := norm_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- the column index of `p` and the frequency along `Pi.single p (latticeBasis)`
  let col : Fin (j + 1) → Fin (r + 1) := fun a => ⟨a, by omega⟩
  let wdir : Idx → Fin (r + 1) → mixedEmbedding.mixedSpace F := fun p =>
    Pi.single (col p.1) (mixedEmbedding.latticeBasis F p.2)
  let L : Idx → ℝ := fun p => colFrequency F β (padRow F (r := r) g0) (wdir p)
  have hwdir : ∀ p, IsColSupported j (wdir p) := by
    intro p a ha
    have hne : a ≠ col p.1 := by
      intro h
      have := congrArg Fin.val h
      simp only [col] at this
      omega
    exact Pi.single_eq_of_ne hne _
  have hwdirB : ∀ p a, ‖wdir p a‖ ≤ ω₀ := by
    intro p a
    by_cases h : a = col p.1
    · subst h
      simp only [wdir, Pi.single_eq_same]
      exact Finset.single_le_sum (f := fun κ => ‖mixedEmbedding.latticeBasis F κ‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ p.2)
    · simp only [wdir, Pi.single_eq_of_ne h, norm_zero]
      exact hω₀0
  -- entry bounds for `y = ρ x`
  have hy : ∀ a b : Fin (r + 1),
      ‖((archCoord F (ratPoint F ρ * x) : ArchimedeanGL F (r + 1)) :
          ArchimedeanMatrix F (r + 1)) a b‖ ≤ n₁ * (T * B) ∧
        ‖(((archCoord F (ratPoint F ρ * x))⁻¹ : ArchimedeanGL F (r + 1)) :
          ArchimedeanMatrix F (r + 1)) a b‖ ≤ n₁ * (T * B) :=
    fun a b => norm_archCoord_ratPoint_mul_apply_le hρ (hB x hx) a b
  -- the per-direction bound
  have hp : ∀ p, |L p| ^ N * Wf ≤ (c₆ * T ^ 2) ^ N * S := by
    intro p
    set Z := colConj F j (ratPoint F ρ * x) (wdir p) with hZ
    have hA : ∀ a b, ‖Z a b‖ ≤ n₁ * (n₁ * (n₁ * (T * B) * ω₀) * (n₁ * (T * B))) :=
      fun a b => norm_colConj_apply_le j (ratPoint F ρ * x) (wdir p) hy (hwdirB p) a b
    have h1 := norm_whittaker_pow_le F hV ψ hψ Z hA N f g
    have h2 := whittaker_pow_deriv_eq F hV ψ hψ hβ hj g0 (ratPoint F ρ * x) (hwdir p) N f
    rw [← hg] at h2
    rw [h2, norm_mul, norm_pow] at h1
    have hnorm : ‖(2 * (π : ℂ) * (L p : ℂ) * Complex.I)‖ = 2 * π * |L p| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos pi_pos, Complex.norm_ofNat, mul_one]
    rw [hnorm] at h1
    have h3 : |L p| ^ N ≤ (2 * π * |L p|) ^ N := by
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ N
      have : 1 ≤ 2 * π := by linarith [pi_gt_three]
      nlinarith [abs_nonneg (L p)]
    have h4 : coordConst F * (n₁ * (n₁ * (n₁ * (T * B) * ω₀) * (n₁ * (T * B)))) = c₆ * T ^ 2 := by
      rw [hc₆]
      ring
    rw [h4] at h1
    calc |L p| ^ N * Wf ≤ (2 * π * |L p|) ^ N * Wf := mul_le_mul_of_nonneg_right h3 hWf0
      _ ≤ _ := h1
  -- the size of the last row is bounded by the frequencies
  have hξ : ‖EqualAnalytic.rowEmbedding F (j + 1)
      ((g0 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j))‖ ≤ K₀ * ∑ p, |L p| := by
    have hsum0 : 0 ≤ ∑ p, |L p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hK₀ hsum0)).mpr fun a => ?_
    have hrow : (g0 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j) a =
        padRow F (r := r) g0 (col a) := by
      simp only [padRow, col, Fin.is_lt, dite_true, Fin.eta]
    change ‖mixedEmbedding F ((g0 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j) a)‖ ≤ _
    rw [hrow]
    refine (hK r (padRow F (r := r) g0) (col a)).trans (mul_le_mul_of_nonneg_left ?_ hK₀)
    calc ∑ k, |colFrequency F β (padRow F (r := r) g0)
          (Pi.single (col a) (mixedEmbedding.latticeBasis F k))| = ∑ k, |L (a, k)| := rfl
      _ ≤ ∑ a' : Fin (j + 1), ∑ k, |L (a', k)| :=
          Finset.single_le_sum (f := fun a' : Fin (j + 1) => ∑ k, |L (a', k)|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)
      _ = ∑ p, |L p| := (Fintype.sum_prod_type (α₁ := Fin (j + 1))
          (α₂ := Module.Free.ChooseBasisIndex ℤ (𝓞 F)) fun p => |L p|).symm
  -- `(1 + Λ)^N ≤ card^N (1 + Σ_p |L_p|^N)`
  have hΛ : (1 + ∑ p, |L p|) ^ N ≤
      (Fintype.card (Option Idx) : ℝ) ^ N * (1 + ∑ p, |L p| ^ N) := by
    have h := sum_pow_le_card_pow_mul_sum_pow (fun o : Option Idx => o.elim 1 fun p => |L p|)
      (fun o => by cases o <;> simp [abs_nonneg]) N
    simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some, one_pow] using h
  have hsize : (1 + ‖EqualAnalytic.rowEmbedding F (j + 1)
      ((g0 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j))‖) ^ N ≤
      (1 + K₀) ^ N * ((Fintype.card (Option Idx) : ℝ) ^ N * (1 + ∑ p, |L p| ^ N)) := by
    have hsum0 : 0 ≤ ∑ p, |L p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h1 : 1 + ‖EqualAnalytic.rowEmbedding F (j + 1)
        ((g0 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j))‖ ≤
        (1 + K₀) * (1 + ∑ p, |L p|) := by nlinarith
    calc _ ≤ ((1 + K₀) * (1 + ∑ p, |L p|)) ^ N :=
          pow_le_pow_left₀ (by positivity) h1 N
      _ = (1 + K₀) ^ N * (1 + ∑ p, |L p|) ^ N := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hΛ (by positivity)
  -- the sum over the word family
  have hfam : ∑ o, ‖whittaker F r ψ ((wordFamily F (R := R) N f o : V) :
      Points F (r + 1) → ℂ) g‖ = Wf + S := by
    rw [Fintype.sum_option]
    rfl
  rw [hfam]
  have hsumL : (∑ p, |L p| ^ N) * Wf ≤ (Fintype.card Idx : ℝ) * ((c₆ * T ^ 2) ^ N * S) := by
    rw [Finset.sum_mul]
    calc ∑ p, |L p| ^ N * Wf ≤ ∑ _p : Idx, (c₆ * T ^ 2) ^ N * S :=
          Finset.sum_le_sum fun p _ => hp p
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hU : 1 ≤ T ^ (2 * N) := one_le_pow₀ hT
  have hcT : (c₆ * T ^ 2) ^ N = c₆ ^ N * T ^ (2 * N) := by rw [mul_pow, ← pow_mul]
  calc _ ≤ (1 + K₀) ^ N * ((Fintype.card (Option Idx) : ℝ) ^ N * (1 + ∑ p, |L p| ^ N)) * Wf :=
        mul_le_mul_of_nonneg_right hsize hWf0
    _ = P * (Wf + (∑ p, |L p| ^ N) * Wf) := by rw [hP]; ring
    _ ≤ P * (Wf + Q * T ^ (2 * N) * S) := by
        refine mul_le_mul_of_nonneg_left ?_ hP0
        have h5 : (Fintype.card Idx : ℝ) * ((c₆ * T ^ 2) ^ N * S) = Q * T ^ (2 * N) * S := by
          rw [hQ, hcT]
          ring
        linarith
    _ ≤ P * (1 + Q) * T ^ (2 * N) * (Wf + S) := by
        rw [mul_assoc P, mul_assoc P]
        refine mul_le_mul_of_nonneg_left ?_ hP0
        have hQU : 0 ≤ Q * T ^ (2 * N) := mul_nonneg hQ0 (zero_le_one.trans hU)
        nlinarith

end Langlands.Global.RankinSelbergGlobal.Unfolding
