import Langlands.HarmonicAnalysis.TorusMonomialDerivative
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SmoothTorusTensorTopology
import Mathlib.Data.List.Induction

/-! # Finite derivative controls for weighted monomial pullbacks -/

noncomputable section

open Langlands.Plancherel Langlands.HarishChandraSchwartz
open scoped NNReal

namespace Langlands.HarmonicAnalysis.TorusFourier

variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K]

/-- Product rule for one angular derivative. -/
theorem torusPartialDeriv_mul {f g : (J → Circle) → ℂ}
    (hf : IsSmoothFiniteTorusFunction f) (hg : IsSmoothFiniteTorusFunction g) (j : J) :
    torusPartialDeriv j (f * g) = torusPartialDeriv j f * g + f * torusPartialDeriv j g := by
  funext z
  simpa only [torusPartialDeriv, Pi.mul_def, Pi.mul_apply, Pi.add_apply, Pi.single_zero,
    finiteTorusExp_zero, mul_one] using ((hasDerivAt_torusTranslate_zero hf j z).mul
    (hasDerivAt_torusTranslate_zero hg j z)).deriv

omit [Fintype J] in
/-- Concatenation composes ordered angular derivatives in their stated order. -/
theorem torusPartialDerivList_append (l m : List J) (f : (J → Circle) → ℂ) :
    torusPartialDerivList (l ++ m) f = torusPartialDerivList l (torusPartialDerivList m f) := by
  simp [torusPartialDerivList, List.foldr_append]

omit [Fintype J] in
@[simp]
theorem torusPartialDerivList_singleton (j : J) (f : (J → Circle) → ℂ) :
    torusPartialDerivList [j] f = torusPartialDeriv j f := rfl

/-- All ordered lists of at most `n` coordinate directions. -/
def torusDerivativeLists (n : ℕ) : Finset (List J) :=
  match n with
  | 0 => {[]}
  | n + 1 => {[]} ∪ Finset.univ.biUnion (fun j : J =>
      (torusDerivativeLists n).image (List.cons j))

/-- Every ordered derivative of the prescribed order is in the finite control set. -/
theorem mem_torusDerivativeLists {n : ℕ} (l : List J) (hl : l.length ≤ n) :
    l ∈ torusDerivativeLists (J := J) n := by
  induction n generalizing l with
  | zero =>
    have : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
    simp [this, torusDerivativeLists]
  | succ n ih =>
    cases l with
    | nil => simp [torusDerivativeLists]
    | cons j l =>
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_univ j, Finset.mem_image.mpr
          ⟨l, ih l (Nat.le_of_succ_le_succ hl), rfl⟩⟩)

/-- One finite supremum of the existing scalar derivative seminorms. -/
def smoothTorusDerivativeControl (n : ℕ) : Seminorm ℂ (smoothFiniteTorusFunctions J) :=
  (torusDerivativeLists (J := J) n).sup (smoothTorusSeminorm J)

theorem norm_torusPartialDerivList_le_control (n : ℕ) (f : smoothFiniteTorusFunctions J)
    (l : List J) (hl : l.length ≤ n) (z : J → Circle) :
    ‖torusPartialDerivList l f.val z‖ ≤ smoothTorusDerivativeControl n f := by
  exact (norm_torusPartialDerivList_le_smoothTorusSeminorm J l f z).trans
    ((Finset.le_sup (f := smoothTorusSeminorm J) (mem_torusDerivativeLists l hl)) f)

/-- A coarse Leibniz bound, using every ordered derivative up to the output order.
The factor `2^length` counts the terms without imposing derivative commutation. -/
theorem norm_torusPartialDerivList_mul_le (l : List J)
    (f g : smoothFiniteTorusFunctions J) (A B : ℝ)
    (hA : 0 ≤ A)
    (hf : ∀ m : List J, m.length ≤ l.length → ∀ z,
      ‖torusPartialDerivList m f.val z‖ ≤ A)
    (hg : ∀ m : List J, m.length ≤ l.length → ∀ z,
      ‖torusPartialDerivList m g.val z‖ ≤ B) (z : J → Circle) :
    ‖torusPartialDerivList l (f.val * g.val) z‖ ≤ (2 : ℝ) ^ l.length * A * B := by
  induction l using List.reverseRecOn generalizing f g with
  | nil =>
    simpa [torusPartialDerivList, norm_mul] using
      mul_le_mul (hf [] le_rfl z) (hg [] le_rfl z) (norm_nonneg _) hA
  | append_singleton l j ih =>
    let df := torusPartialDerivLinear j f
    let dg := torusPartialDerivLinear j g
    have hf0 (m : List J) (hm : m.length ≤ l.length) :=
      hf m (hm.trans (by simp))
    have hg0 (m : List J) (hm : m.length ≤ l.length) :=
      hg m (hm.trans (by simp))
    have hdf (m : List J) (hm : m.length ≤ l.length) (y : J → Circle) :
        ‖torusPartialDerivList m df.val y‖ ≤ A := by
      change ‖torusPartialDerivList m (torusPartialDeriv j f.val) y‖ ≤ A
      simpa only [torusPartialDerivList_append, torusPartialDerivList_singleton]
        using hf (m ++ [j]) (by simpa using hm) y
    have hdg (m : List J) (hm : m.length ≤ l.length) (y : J → Circle) :
        ‖torusPartialDerivList m dg.val y‖ ≤ B := by
      change ‖torusPartialDerivList m (torusPartialDeriv j g.val) y‖ ≤ B
      simpa only [torusPartialDerivList_append, torusPartialDerivList_singleton]
        using hg (m ++ [j]) (by simpa using hm) y
    rw [torusPartialDerivList_append]
    change ‖torusPartialDerivList l (torusPartialDeriv j (f.val * g.val)) z‖ ≤ _
    rw [torusPartialDeriv_mul f.property g.property]
    have hadd : torusPartialDerivList l (df.val * g.val + f.val * dg.val) =
        torusPartialDerivList l (df.val * g.val) +
          torusPartialDerivList l (f.val * dg.val) := by
      simpa only [torusPartialDerivListLinear_apply, Subalgebra.coe_add, Subalgebra.coe_mul]
        using congrArg Subtype.val
          ((torusPartialDerivListLinear l).map_add (df * g) (f * dg))
    change ‖torusPartialDerivList l (df.val * g.val + f.val * dg.val) z‖ ≤ _
    rw [hadd, Pi.add_apply]
    have h1 := ih df g hdf hg0
    have h2 := ih f dg hf0 hdg
    calc ‖torusPartialDerivList l (df.val * g.val) z +
          torusPartialDerivList l (f.val * dg.val) z‖
        ≤ ‖torusPartialDerivList l (df.val * g.val) z‖ +
          ‖torusPartialDerivList l (f.val * dg.val) z‖ := norm_add_le _ _
      _ ≤ (2 : ℝ) ^ l.length * A * B + (2 : ℝ) ^ l.length * A * B := add_le_add h1 h2
      _ = (2 : ℝ) ^ (l ++ [j]).length * A * B := by
        simp only [List.length_append, List.length_singleton, pow_succ]
        ring

/-- The monomial directional derivative on smooth scalar functions. -/
def monomialPartialDerivLinear (a : J → K → ℤ) (k : K) :
    smoothFiniteTorusFunctions J →ₗ[ℂ] smoothFiniteTorusFunctions J :=
  ∑ j, (a j k : ℂ) • torusPartialDerivLinear j

omit [Fintype K] in
@[simp]
theorem monomialPartialDerivLinear_apply (a : J → K → ℤ) (k : K)
    (f : smoothFiniteTorusFunctions J) :
    (monomialPartialDerivLinear a k f).val = monomialPartialDeriv a k f.val := by
  funext z
  simp [monomialPartialDerivLinear, monomialPartialDeriv, torusPartialDerivLinear]

omit [Fintype K] in
/-- Iteration of the smooth linear operator is the existing pointwise iterate. -/
theorem monomialPartialDerivLinear_pow_apply (a : J → K → ℤ) (k : K) (n : ℕ)
    (f : smoothFiniteTorusFunctions J) :
    ((monomialPartialDerivLinear a k ^ n) f).val =
      (monomialPartialDeriv a k)^[n] f.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change (monomialPartialDerivLinear a k ((monomialPartialDerivLinear a k ^ n) f)).val = _
    rw [monomialPartialDerivLinear_apply, ih, Function.iterate_succ_apply']

omit [Fintype K] in
/-- Bounds for ordered derivatives control a repeated monomial directional derivative. -/
theorem norm_monomialPartialDeriv_iterate_le (a : J → K → ℤ) (k : K) (n : ℕ)
    (f : smoothFiniteTorusFunctions J) (M : ℝ)
    (hf : ∀ l : List J, l.length ≤ n → ∀ z, ‖torusPartialDerivList l f.val z‖ ≤ M)
    (z : J → Circle) :
    ‖(monomialPartialDeriv a k)^[n] f.val z‖ ≤
      (∑ j, ‖(a j k : ℂ)‖) ^ n * M := by
  rw [← monomialPartialDerivLinear_pow_apply]
  induction n generalizing f with
  | zero => simpa [torusPartialDerivList] using hf [] le_rfl z
  | succ n ih =>
    have hd (j : J) (l : List J) (hl : l.length ≤ n) (y : J → Circle) :
        ‖torusPartialDerivList l (torusPartialDerivLinear j f).val y‖ ≤ M := by
      change ‖torusPartialDerivList l (torusPartialDeriv j f.val) y‖ ≤ M
      simpa only [torusPartialDerivList_append, torusPartialDerivList_singleton]
        using hf (l ++ [j]) (by simpa using hl) y
    have heq : ((monomialPartialDerivLinear a k ^ (n + 1)) f).val z =
        ∑ j, (a j k : ℂ) * ((monomialPartialDerivLinear a k ^ n)
          (torusPartialDerivLinear j f)).val z := by
      rw [pow_succ]
      change ((monomialPartialDerivLinear a k ^ n) (monomialPartialDerivLinear a k f)).val z = _
      simp [monomialPartialDerivLinear, map_sum, map_smul]
    rw [heq]
    calc ‖∑ j, (a j k : ℂ) * ((monomialPartialDerivLinear a k ^ n)
            (torusPartialDerivLinear j f)).val z‖
        ≤ ∑ j, ‖(a j k : ℂ) * ((monomialPartialDerivLinear a k ^ n)
            (torusPartialDerivLinear j f)).val z‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖(a j k : ℂ)‖ * ((∑ i, ‖(a i k : ℂ)‖) ^ n * M) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (ih (torusPartialDerivLinear j f) (hd j)) (norm_nonneg _)
      _ = (∑ j, ‖(a j k : ℂ)‖) ^ (n + 1) * M := by
        rw [← Finset.sum_mul, pow_succ]
        ring

/-- A product's derivatives up to order `n` are bounded by a product of two finite
suprema of the existing scalar seminorms. -/
theorem norm_torusPartialDerivList_mul_le_control (n : ℕ)
    (W f : smoothFiniteTorusFunctions J) (l : List J) (hl : l.length ≤ n)
    (z : J → Circle) :
    ‖torusPartialDerivList l (W.val * f.val) z‖ ≤
      (2 : ℝ) ^ n * smoothTorusDerivativeControl n W * smoothTorusDerivativeControl n f := by
  refine (norm_torusPartialDerivList_mul_le l W f
    (smoothTorusDerivativeControl n W) (smoothTorusDerivativeControl n f)
    (apply_nonneg (smoothTorusDerivativeControl n) W)
    (fun m hm y => norm_torusPartialDerivList_le_control n W m (hm.trans hl) y)
    (fun m hm y => norm_torusPartialDerivList_le_control n f m (hm.trans hl) y) z).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hl)
      (apply_nonneg (smoothTorusDerivativeControl n) W))
    (apply_nonneg (smoothTorusDerivativeControl n) f)

/-- One constant controls the weighted monomial pullback and all its `n`th pure
angular derivatives, uniformly over every scalar input and every translate. -/
theorem exists_weighted_monomial_derivative_control [DecidableEq K]
    (W : smoothFiniteTorusFunctions J) (a : J → K → ℤ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (f : smoothFiniteTorusFunctions J) (y : J → Circle) (z : K → Circle),
        ‖W.val (finiteTorusMonomial a z * y) * f.val (finiteTorusMonomial a z * y)‖ ≤
          C * smoothTorusDerivativeControl n f) ∧
      ∀ (f : smoothFiniteTorusFunctions J) (y : J → Circle) (k : K) (z : K → Circle),
        ‖(torusPartialDeriv k)^[n]
          (fun z => W.val (finiteTorusMonomial a z * y) *
            f.val (finiteTorusMonomial a z * y)) z‖ ≤
          C * smoothTorusDerivativeControl n f := by
  let A : K → ℝ := fun k => (∑ j, ‖(a j k : ℂ)‖) ^ n
  let C₀ : ℝ := (2 : ℝ) ^ n * smoothTorusDerivativeControl n W
  let D : ℝ := 1 + ∑ k, A k
  have hA (k : K) : 0 ≤ A k := by dsimp [A]; positivity
  have hC₀ : 0 ≤ C₀ := mul_nonneg (by positivity) (apply_nonneg (smoothTorusDerivativeControl n) W)
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hA k)
  have hAD (k : K) : A k ≤ D :=
    (Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ k)).trans
      (le_add_of_nonneg_left (by norm_num))
  have hprod (f : smoothFiniteTorusFunctions J) (l : List J) (hl : l.length ≤ n)
      (x : J → Circle) :
      ‖torusPartialDerivList l (W.val * f.val) x‖ ≤
        C₀ * smoothTorusDerivativeControl n f :=
    norm_torusPartialDerivList_mul_le_control n W f l hl x
  refine ⟨C₀ * D, mul_nonneg hC₀ (le_trans (by norm_num) hD), ?_, ?_⟩
  · intro f y z
    have h := hprod f [] (Nat.zero_le n) (finiteTorusMonomial a z * y)
    change ‖W.val _ * f.val _‖ ≤ _ at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right hC₀ hD) (apply_nonneg (smoothTorusDerivativeControl n) f))
  · intro f y k z
    have heq := iterate_torusPartialDeriv_comp_monomial_mul (W * f).property a y k n
    change (torusPartialDeriv k)^[n]
      (fun z => W.val (finiteTorusMonomial a z * y) *
        f.val (finiteTorusMonomial a z * y)) =
      (fun z => (monomialPartialDeriv a k)^[n] (W.val * f.val)
        (finiteTorusMonomial a z * y)) at heq
    rw [heq]
    calc ‖(monomialPartialDeriv a k)^[n] (W.val * f.val)
          (finiteTorusMonomial a z * y)‖
        ≤ A k * (C₀ * smoothTorusDerivativeControl n f) :=
          norm_monomialPartialDeriv_iterate_le a k n (W * f)
            (C₀ * smoothTorusDerivativeControl n f) (hprod f) _
      _ ≤ D * (C₀ * smoothTorusDerivativeControl n f) :=
        mul_le_mul_of_nonneg_right (hAD k)
          (mul_nonneg hC₀ (apply_nonneg (smoothTorusDerivativeControl n) f))
      _ = C₀ * D * smoothTorusDerivativeControl n f := by ring

end Langlands.HarmonicAnalysis.TorusFourier
