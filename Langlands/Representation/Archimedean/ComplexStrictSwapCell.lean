import Langlands.Representation.Archimedean.ComplexStrictSwapChain
import Mathlib.Tactic.Group

/-! # The lower unipotent form of a strict complex swap chart -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean.ComplexSwapJacquet.StrictSwapChain

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

variable {n m : ℕ} {ds es : List ComplexCharacterData}

local notation "P" => Langlands.GeneralLinear.permutation n ℂ

/-- The permutation from the chain, carrying the final positions back to the
initial positions. -/
def permutation : {ds es : List ComplexCharacterData} → {m : ℕ} →
    StrictSwapChain n ds es m → Equiv.Perm (Fin n)
  | _, _, _, .nil _ => 1
  | _, _, _, .cons _ _ _ _ _ i j _ _ _ tail => Equiv.swap i j * tail.permutation

private theorem swap_eq_permutation (i j : Fin n) :
    Matrix.GeneralLinearGroup.swap ℂ i j = P (Equiv.swap i j) := by
  apply Units.ext
  have hinv : (Equiv.swap i j)⁻¹ = Equiv.swap i j := Equiv.symm_swap i j
  rw [permutation_coe, hinv]
  rfl

theorem chartProduct_zero (w : StrictSwapChain n ds es m) :
    w.chartProduct (fun _ => 0) = P w.permutation := by
  induction w with
  | nil => simp [chartProduct, permutation]
  | @cons pre post d e hn i j hi hj hre fs m tail ih =>
    have hchart : chart i j hj 0 = P (Equiv.swap i j) := by
      apply Units.ext
      rw [chart_val, Matrix.transvection_zero, mul_one, ← swap_eq_permutation]
      rfl
    simp only [chartProduct, permutation, hchart, ih, map_mul]

private theorem conjugate_transvection_mem_lower {i j : Fin n} (hij : i ≠ j)
    (σ : Equiv.Perm (Fin n)) (hσ : σ j < σ i) (z : ℂ) :
    P σ * Matrix.GeneralLinearGroup.transvection i j hij z * (P σ)⁻¹ ∈ lowerUnipotent n ℂ := by
  rw [mem_lowerUnipotent_iff]
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [permutation_conjugate_entry]
    change Matrix.transvection i j z (σ.symm a) (σ.symm b) = 0
    have hab' : σ.symm a ≠ σ.symm b := fun h => hab.ne (σ.symm.injective h)
    have hzero : ¬(i = σ.symm a ∧ j = σ.symm b) := by
      rintro ⟨hi, hj⟩
      have ha : σ i = a := by simpa using congrArg σ hi
      have hb : σ j = b := by simpa using congrArg σ hj
      rw [ha, hb] at hσ
      exact hab.not_gt hσ
    simp [Matrix.transvection, Matrix.one_apply_ne hab', hzero]
  · rw [permutation_conjugate_entry]
    change Matrix.transvection i j z (σ.symm a) (σ.symm a) = 1
    have hzero : ¬(i = σ.symm a ∧ j = σ.symm a) := fun h => hij (h.1.trans h.2.symm)
    simp [Matrix.transvection, hzero]

private theorem posExponent_adjacent_swap (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (hn : (pre ++ d :: e :: post).length = n)
    (i j : Fin n) (hi : (i : ℕ) = pre.length) (hj : (j : ℕ) = i + 1) (k : Fin n) :
    posExponent (pre ++ e :: d :: post) k =
      posExponent (pre ++ d :: e :: post) (Equiv.swap i j k) := by
  have hs : ComplexPermutation.swapPerm pre post d e hn = Equiv.swap i j := by
    have h₁ : (⟨pre.length, by rw [← hn]; simp⟩ : Fin n) = i := Fin.ext hi.symm
    have h₂ : (⟨pre.length + 1, by rw [← hn]; simp⟩ : Fin n) = j := Fin.ext (by
      change pre.length + 1 = (j : ℕ)
      omega)
    rw [ComplexPermutation.swapPerm, h₁, h₂]
  have hes := (ComplexPermutation.length_swap pre post d e).trans hn
  rw [posExponent_eq_get _ _ (hes.symm ▸ k.2),
    posExponent_eq_get _ _ (hn.symm ▸ (Equiv.swap i j k).2)]
  have h := ComplexPermutation.get_swap pre post d e hn k
  rw [hs, Equiv.symm_swap] at h
  exact congrArg ComplexCharacterData.exponent h.symm

set_option maxHeartbeats 800000 in
private theorem prefixed_chartProduct_mem_lower (w : StrictSwapChain n ds es m)
    {weight : Fin n → ℝ} (hweight : Antitone weight) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ k : Fin n, (posExponent ds k).re = weight (σ k)) (z : Fin m → ℂ) :
    P σ * w.chartProduct z * (P (σ * w.permutation))⁻¹ ∈ lowerUnipotent n ℂ := by
  induction w generalizing σ with
  | nil =>
    change P σ * 1 * (P (σ * 1))⁻¹ ∈ lowerUnipotent n ℂ
    rw [mul_one (P σ), mul_one σ, mul_inv_cancel]
    exact (lowerUnipotent n ℂ).one_mem
  | @cons pre post d e hn i j hi hj hre fs m tail ih =>
    let s := Equiv.swap i j
    have hjval : (j : ℕ) = pre.length + 1 := by omega
    have hlt : weight (σ j) < weight (σ i) := by
      rw [← hσ j, ← hσ i, hi, hjval, posExponent_append_cons, posExponent_append_cons_succ]
      exact sub_pos.mp (by simpa only [Complex.sub_re] using hre)
    have hσlt : σ i < σ j := lt_of_not_ge fun h => (not_lt_of_ge (hweight h)) hlt
    have horder : (σ * s) j < (σ * s) i := by
      simpa only [Equiv.Perm.mul_apply, s, Equiv.swap_apply_left, Equiv.swap_apply_right] using hσlt
    have hnext (k : Fin n) : (posExponent (pre ++ e :: d :: post) k).re = weight ((σ * s) k) := by
      rw [posExponent_adjacent_swap pre post d e hn i j hi hj k]
      exact hσ (s k)
    let x := Matrix.GeneralLinearGroup.transvection i j (ne_of_val_eq_succ hj) (z 0)
    let tailChart := tail.chartProduct (fun k => z k.succ)
    have htail : P (σ * s) * tailChart * (P ((σ * s) * tail.permutation))⁻¹ ∈ lowerUnipotent n ℂ :=
      ih (σ * s) hnext (fun k => z k.succ)
    have hhead : P (σ * s) * x * (P (σ * s))⁻¹ ∈ lowerUnipotent n ℂ :=
      conjugate_transvection_mem_lower (ne_of_val_eq_succ hj) (σ * s) horder (z 0)
    have hchart : chart i j hj (z 0) = P s * x := by
      change Matrix.GeneralLinearGroup.swap ℂ i j * x = P s * x
      rw [swap_eq_permutation]
    change P σ * (chart i j hj (z 0) * tailChart) *
      (P (σ * (s * tail.permutation)))⁻¹ ∈ lowerUnipotent n ℂ
    rw [hchart, ← mul_assoc σ s tail.permutation]
    have hgroup :
        P σ * (P s * x * tailChart) * (P ((σ * s) * tail.permutation))⁻¹ =
          (P (σ * s) * x * (P (σ * s))⁻¹) *
            (P (σ * s) * tailChart * (P ((σ * s) * tail.permutation))⁻¹) := by
      simp only [map_mul]
      group
    rw [hgroup]
    exact mul_mem hhead htail

/-- For a Langlands-ordered source the strict swap chart lies in the lower
unipotent group after removing its final permutation on the right. -/
theorem chartProduct_mul_permutation_inv_mem_lower (w : StrictSwapChain n ds es m)
    (hn : ds.length = n) (ho : IsComplexLanglandsOrdered ds) (z : Fin m → ℂ) :
    w.chartProduct z * (P w.permutation)⁻¹ ∈ lowerUnipotent n ℂ := by
  let weight (k : Fin n) := (posExponent ds k).re
  have hweight : Antitone weight := by
    intro a b hab
    rcases eq_or_lt_of_le hab with rfl | hab
    · exact le_rfl
    · change (posExponent ds b).re ≤ (posExponent ds a).re
      rw [posExponent_eq_get _ _ (hn.symm ▸ b.2), posExponent_eq_get _ _ (hn.symm ▸ a.2)]
      exact List.Pairwise.rel_get_of_lt ho (show Fin.cast hn.symm a < Fin.cast hn.symm b from hab)
  simpa only [map_one, one_mul] using
    prefixed_chartProduct_mem_lower w hweight 1 (fun _ => rfl) z

end Langlands.Archimedean.ComplexSwapJacquet.StrictSwapChain
