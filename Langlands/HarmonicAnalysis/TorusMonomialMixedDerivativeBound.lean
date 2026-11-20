import Langlands.HarmonicAnalysis.TorusMonomialSeminormControl

/-! # Mixed angular derivatives of a monomial pullback -/

noncomputable section

open Langlands.Plancherel Langlands.HarishChandraSchwartz

namespace Langlands.HarmonicAnalysis.TorusFourier

universe uJ uK

variable {J : Type uJ} {K : Type uK} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

/-- Pullback of smooth scalar functions by an integer monomial map. -/
def smoothTorusMonomialPullback (a : J → K → ℤ) :
    smoothFiniteTorusFunctions J →ₗ[ℂ] smoothFiniteTorusFunctions K where
  toFun f := ⟨f.val ∘ finiteTorusMonomial a, f.property.comp_monomial a⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq J] [DecidableEq K] in
@[simp]
theorem smoothTorusMonomialPullback_apply (a : J → K → ℤ)
    (f : smoothFiniteTorusFunctions J) (z : K → Circle) :
    (smoothTorusMonomialPullback a f).val z = f.val (finiteTorusMonomial a z) := rfl

/-- Each ordered mixed derivative of the pullback is controlled by source
angular derivatives up to the same order. No commutation of the orders is used. -/
theorem norm_torusPartialDerivList_comp_monomial_le (a : J → K → ℤ)
    (l : List K) (f : smoothFiniteTorusFunctions J) (M : ℝ)
    (hf : ∀ m : List J, m.length ≤ l.length → ∀ z, ‖torusPartialDerivList m f.val z‖ ≤ M)
    (z : K → Circle) :
    ‖torusPartialDerivList l (f.val ∘ finiteTorusMonomial a) z‖ ≤
      (l.map fun k => ∑ j, ‖(a j k : ℂ)‖).prod * M := by
  induction l using List.reverseRecOn generalizing f M with
  | nil => simpa [torusPartialDerivList] using hf [] le_rfl (finiteTorusMonomial a z)
  | append_singleton l k ih =>
    let T := monomialPartialDerivLinear a k
    let A : ℝ := ∑ j, ‖(a j k : ℂ)‖
    have hchain : torusPartialDeriv k (f.val ∘ finiteTorusMonomial a) =
        (T f).val ∘ finiteTorusMonomial a := by
      funext y
      simpa only [T, monomialPartialDerivLinear_apply, Function.comp_def, mul_one] using
        torusPartialDeriv_comp_monomial_mul f.property a 1 k y
    have hT (m : List J) (hm : m.length ≤ l.length) (x : J → Circle) :
        ‖torusPartialDerivList m (T f).val x‖ ≤ A * M := by
      have hsum : torusPartialDerivList m (T f).val x =
          ∑ j, (a j k : ℂ) * torusPartialDerivList (m ++ [j]) f.val x := by
        rw [← torusPartialDerivListLinear_apply]
        simp [T, monomialPartialDerivLinear, torusPartialDerivList_append, torusPartialDerivLinear]
      rw [hsum, show A * M = ∑ j, ‖(a j k : ℂ)‖ * M from Finset.sum_mul _ _ _]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf (m ++ [j]) (by simpa using hm) x) (norm_nonneg _)
    rw [torusPartialDerivList_append, torusPartialDerivList_singleton, hchain]
    simpa only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc, A] using ih (T f) (A * M) hT

/-- The existing scalar derivative seminorm of a monomial pullback is bounded
by the finite supremum of source seminorms up to that order. -/
theorem smoothTorusSeminorm_monomialPullback_le (a : J → K → ℤ)
    (l : List K) (f : smoothFiniteTorusFunctions J) :
    smoothTorusSeminorm K l (smoothTorusMonomialPullback a f) ≤
      (l.map fun k => ∑ j, ‖(a j k : ℂ)‖).prod * smoothTorusDerivativeControl l.length f := by
  have hprod : 0 ≤ (l.map fun k => ∑ j, ‖(a j k : ℂ)‖).prod := by
    apply List.prod_nonneg
    intro r hr
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  exact (smoothTorusSeminorm_le_iff K l _ (mul_nonneg hprod (apply_nonneg _ _))).mpr
    (norm_torusPartialDerivList_comp_monomial_le a l f _
      (norm_torusPartialDerivList_le_control l.length f))

end Langlands.HarmonicAnalysis.TorusFourier
