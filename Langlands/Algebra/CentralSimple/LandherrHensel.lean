import Langlands.Global.CompletionIntegersSmoothPointLifting
import Langlands.Global.CompletionResidueAdic
import Mathlib.FieldTheory.Finite.Basic

/-! # Binary norm equations with unit coefficients at a finite completion -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open NumberField IsDedekindDomain Polynomial IsLocalRing
open scoped Valued

universe u

/-- At a finite place of a number field where `2`, `a` and `b` are units, the equation
`x² - a y² = b` is solvable in the completion: solve it in the finite residue field of odd
characteristic and lift a simple root by Hensel's lemma. -/
theorem exists_sq_sub_mul_sq_of_units {K : Type u} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (a b : P.adicCompletion K) (ha : Valued.v a = 1)
    (hb : Valued.v b = 1) (h2 : Valued.v (2 : P.adicCompletion K) = 1) :
    ∃ x y : P.adicCompletion K, x ^ 2 - a * y ^ 2 = b := by
  classical
  let O := P.adicCompletionIntegers K
  have : HenselianLocalRing O := Global.adicCompletionIntegers_henselian (𝓞 K) K P
  have hmem : ∀ z : P.adicCompletion K, Valued.v z = 1 → z ∈ O := fun z hz =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P).mpr hz.le
  let a' : O := ⟨a, hmem a ha⟩
  let b' : O := ⟨b, hmem b hb⟩
  have ha' : IsUnit a' := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr ha
  have hb' : IsUnit b' := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hb
  have h2' : IsUnit (2 : O) := by
    apply HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr
    have : ((2 : O) : P.adicCompletion K) = 2 := by norm_cast
    rw [this]
    exact h2
  let k := ResidueField O
  have : Fintype k := Fintype.ofFinite k
  have hak : residue O a' ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr ha'
  have hbk : residue O b' ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr hb'
  have h2k : (2 : k) ≠ 0 := by
    have := (residue_ne_zero_iff_isUnit (2 : O)).mpr h2'
    rwa [map_ofNat] at this
  have hchar : ringChar k ≠ 2 := by
    intro h
    apply h2k
    have : CharP k 2 := h ▸ ringChar.charP k
    exact CharP.cast_eq_zero k 2
  have hcard := FiniteField.odd_card_of_char_ne_two hchar
  have hf : (X ^ 2 - C (residue O b')).degree = 2 := by
    rw [degree_sub_C (by rw [degree_X_pow]; norm_num), degree_X_pow]; rfl
  have hg : (-C (residue O a') * X ^ 2).degree = 2 := by
    rw [degree_mul, degree_neg, degree_C hak, degree_X_pow, zero_add]; rfl
  obtain ⟨x₀, y₀, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul, eval_neg] at hxy
  obtain ⟨x₁, rfl⟩ := residue_surjective x₀
  obtain ⟨y₁, rfl⟩ := residue_surjective y₀
  have hev : ∀ c z : O, (X ^ 2 - C c : O[X]).eval z = z ^ 2 - c := fun c z => by
    rw [eval_sub, eval_pow, eval_X, eval_C]
  have hder : ∀ c z : O, (X ^ 2 - C c : O[X]).derivative.eval z = 2 * z := fun c z => by
    rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul, eval_C, eval_pow,
      eval_X]
    norm_num
  by_cases hx0 : residue O x₁ = 0
  · -- solve for `y` with `x = x₁`
    have hy0 : residue O y₁ ≠ 0 := by
      intro hy
      rw [hx0, hy] at hxy
      apply hbk
      linear_combination -hxy
    obtain ⟨ai, hai⟩ := ha'.exists_left_inv
    let G : O[X] := X ^ 2 - C (ai * (x₁ ^ 2 - b'))
    have hGm : G.Monic := monic_X_pow_sub_C _ (by norm_num)
    have hGe : G.eval y₁ ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff, hev, map_sub, map_mul, map_sub, map_pow, map_pow]
      have hai' : residue O ai * residue O a' = 1 := by rw [← map_mul, hai, map_one]
      linear_combination -(residue O ai) * hxy - (residue O y₁ ^ 2) * hai'
    have hGd : IsUnit (G.derivative.eval y₁) := by
      rw [hder, ← residue_ne_zero_iff_isUnit, map_mul, map_ofNat]
      exact mul_ne_zero h2k hy0
    obtain ⟨y, hy, -⟩ := HenselianLocalRing.is_henselian G hGm y₁ hGe hGd
    refine ⟨x₁, y, ?_⟩
    have hy' : y ^ 2 = ai * (x₁ ^ 2 - b') := by
      have := hy.eq_zero
      rw [hev] at this
      linear_combination this
    have h := congrArg (fun z : O => (z : P.adicCompletion K)) (show x₁ ^ 2 - a' * y ^ 2 = b' by
      rw [hy', ← mul_assoc, mul_comm a' ai, hai, one_mul]; ring)
    simpa [a', b'] using h
  · -- solve for `x` with `y = y₁`
    let G : O[X] := X ^ 2 - C (b' + a' * y₁ ^ 2)
    have hGm : G.Monic := monic_X_pow_sub_C _ (by norm_num)
    have hGe : G.eval x₁ ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff, hev, map_sub, map_add, map_mul, map_pow, map_pow]
      linear_combination hxy
    have hGd : IsUnit (G.derivative.eval x₁) := by
      rw [hder, ← residue_ne_zero_iff_isUnit, map_mul, map_ofNat]
      exact mul_ne_zero h2k hx0
    obtain ⟨x, hx, -⟩ := HenselianLocalRing.is_henselian G hGm x₁ hGe hGd
    refine ⟨x, y₁, ?_⟩
    have hx' : x ^ 2 - a' * y₁ ^ 2 = b' := by
      have := hx.eq_zero
      rw [hev] at this
      linear_combination this
    have h := congrArg (fun z : O => (z : P.adicCompletion K)) hx'
    simpa [a', b'] using h

end Langlands.CentralSimple.Landherr
