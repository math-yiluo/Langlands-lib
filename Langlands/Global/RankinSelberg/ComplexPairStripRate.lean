import Langlands.LocalFactor.Archimedean.GammaStripGrowth
import Langlands.Global.RankinSelberg.ComplexCompactProfileFamily

/-! # A common reciprocal Gamma rate on all real strips of compact inducing families -/

noncomputable section

open Set
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open Langlands.Archimedean (characterOfParams characterOfParams_weight characterOfParams_exponent)
open ComplexCompactProfileFamily (characterList)

private def gammaShift (d : ComplexCharacterData) : ℂ := d.exponent + (d.weight.natAbs : ℂ) / 2

private theorem norm_complexLFactor_denominator_le_exp (u v R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ds : List ComplexCharacterData,
      (∀ d ∈ ds, ‖gammaShift d‖ ≤ R) → ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
        ‖(complexLFactor ds).denominator s‖ ≤ A ^ ds.length *
          Real.exp (((ds.length : ℝ) * Real.pi) * |s.im|) := by
  obtain ⟨C, hC, h⟩ := norm_gammaComplex_denominator_le_exp (u - R) (v + R)
  let A := C * Real.exp (Real.pi * R)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, fun ds => ?_⟩
  induction ds with
  | nil =>
    intro _ s _ _
    simp [complexLFactor_nil, ReciprocalEntire.one]
  | cons d ds ih =>
    intro hd s hu hv
    have hs := hd d List.mem_cons_self
    have ho := ih (fun e he => hd e (List.mem_cons_of_mem _ he)) s hu hv
    have hlo := abs_le.mp ((Complex.abs_re_le_norm (gammaShift d)).trans hs)
    have him := (Complex.abs_im_le_norm (gammaShift d)).trans hs
    have hD : ‖d.lFactor.denominator s‖ ≤ A * Real.exp (Real.pi * |s.im|) := by
      change ‖gammaComplex.denominator (s + gammaShift d)‖ ≤ _
      have h' := h (s + gammaShift d) (by rw [Complex.add_re]; linarith [hlo.1])
        (by rw [Complex.add_re]; linarith [hlo.2])
      refine h'.trans ?_
      dsimp only [A]
      rw [mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
      rw [Complex.add_im]
      have hi := (abs_add_le s.im (gammaShift d).im).trans (add_le_add le_rfl him)
      linarith [mul_le_mul_of_nonneg_left hi Real.pi_pos.le]
    rw [complexLFactor_cons, ReciprocalEntire.denominator_mul, norm_mul]
    refine (mul_le_mul hD ho (norm_nonneg _) (by positivity)).trans_eq ?_
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, pow_succ]
    rw [show ((ds.length : ℝ) + 1) * Real.pi * |s.im| =
      Real.pi * |s.im| + ((ds.length : ℝ) * Real.pi) * |s.im| by ring, Real.exp_add]
    ring

private theorem norm_pair_denominator_ofFn {X : Type*} [TopologicalSpace X]
    {n m : ℕ} (S : Set X) (hS : IsCompact S) (x : X → Fin n → ComplexCharacterData)
    (y : X → Fin m → ComplexCharacterData)
    (h : ∀ i j, Continuous (fun z => gammaShift ((x z i).mul (y z j)))) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ S, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖(complexPairLFactor (List.ofFn (x z)) (List.ofFn (y z))).denominator s‖ ≤
        C * Real.exp (((n * m : ℕ) : ℝ) * Real.pi * |s.im|) := by
  choose B hB using fun i j => hS.exists_bound_of_continuousOn (h i j).continuousOn
  let R := ∑ i : Fin n, ∑ j : Fin m, max (B i j) 0
  obtain ⟨A, hA, hA'⟩ := norm_complexLFactor_denominator_le_exp a b R
  refine ⟨A ^ (n * m), pow_nonneg hA _, fun z hz s hs ht => ?_⟩
  let ds := complexPairBlocks (List.ofFn (x z)) (List.ofFn (y z))
  have hlen : ds.length = n * m := by simp [ds, length_complexPairBlocks]
  have hshift (d : ComplexCharacterData) (hd : d ∈ ds) : ‖gammaShift d‖ ≤ R := by
    change d ∈ (List.ofFn (x z)).flatMap (fun e => (List.ofFn (y z)).map e.mul) at hd
    obtain ⟨e, he, hde⟩ := List.mem_flatMap.mp hd
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hde
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
    exact ((hB i j z hz).trans (le_max_left _ _)).trans <|
      (Finset.single_le_sum (fun j _ => le_max_right (B i j) 0) (Finset.mem_univ j)).trans <|
        Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun j _ => le_max_right (B k j) 0)
          (Finset.mem_univ i)
  have h := hA' ds hshift s hs ht
  rw [hlen] at h
  exact h

/-- On a compact inducing parameter set, both pair denominators have the same
exponential rate on every spectral strip. The number of blocks is `n * m`. -/
def ComplexPairStripRateStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (S : Set X), IsCompact S →
    ∀ (n m : ℕ) (l : Fin n → ℤ) (k : Fin m → ℤ)
      (p : X → Fin n → ℂ) (q : X → Fin m → ℂ), Continuous p → Continuous q →
    ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ S, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖(complexPairLFactor (characterList l (p z)) (characterList k (q z))).denominator s‖ ≤
        C * Real.exp (((n * m : ℕ) : ℝ) * Real.pi * |s.im|) ∧
      ‖(complexPairLFactor ((characterList l (p z)).map ComplexCharacterData.inv)
        ((characterList k (q z)).map ComplexCharacterData.inv)).denominator s‖ ≤
        C * Real.exp (((n * m : ℕ) : ℝ) * Real.pi * |s.im|)

set_option maxHeartbeats 500000 in
theorem complexPairStripRate : ComplexPairStripRateStatement := by
  intro X _ S hS n m l k p q hp hq a b
  let x (z : X) (i : Fin n) := characterOfParams (l i) (p z i)
  let y (z : X) (j : Fin m) := characterOfParams (k j) (q z j)
  have hb (i : Fin n) (j : Fin m) :
      Continuous (fun z => gammaShift ((x z i).mul (y z j))) := by
    simp only [x, y, gammaShift, ComplexCharacterData.mul, characterOfParams_exponent,
      characterOfParams_weight]
    exact ((continuous_apply i).comp hp).add ((continuous_apply j).comp hq) |>.add continuous_const
  have hbd (i : Fin n) (j : Fin m) :
      Continuous (fun z => gammaShift ((x z i).inv.mul (y z j).inv)) := by
    simp only [x, y, gammaShift, ComplexCharacterData.mul, ComplexCharacterData.inv_exponent,
      ComplexCharacterData.inv_weight, characterOfParams_exponent, characterOfParams_weight]
    exact (((continuous_apply i).comp hp).neg.add (((continuous_apply j).comp hq).neg)).add continuous_const
  obtain ⟨C, hC, hCp⟩ := norm_pair_denominator_ofFn S hS x y hb a b
  obtain ⟨D, hD, hDp⟩ := norm_pair_denominator_ofFn S hS (fun z i => (x z i).inv)
    (fun z j => (y z j).inv) hbd a b
  refine ⟨max C D, hC.trans (le_max_left _ _), fun z hz s hs ht => ?_⟩
  have h := (hDp z hz s hs ht).trans (mul_le_mul_of_nonneg_right (le_max_right C D) (Real.exp_pos _).le)
  refine ⟨(hCp z hz s hs ht).trans (mul_le_mul_of_nonneg_right (le_max_left C D) (Real.exp_pos _).le), ?_⟩
  simp only [characterList, List.map_ofFn]
  exact h

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
