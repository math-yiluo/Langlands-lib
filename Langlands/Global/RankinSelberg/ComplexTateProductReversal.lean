import Langlands.Global.RankinSelberg.ComplexTateProductContinuation

/-! # Reversal of the diagonal variables in the normalized product Tate integral -/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped SchwartzMap Topology

namespace Langlands.Global.RankinSelbergGlobal.ComplexTateProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "Z" => Fin n → ℂ
local notation "W" => Fin n → ℤ

private def reverseEquiv : Z ≃L[ℝ] Z :=
  let L : Z →ₗ[ℝ] Z :=
    { toFun := fun z => z ∘ Fin.rev
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  (LinearEquiv.ofInvolutive L fun z => by
    funext j
    change z j.rev.rev = z j
    rw [Fin.rev_rev]).toContinuousLinearEquiv

/-- Pullback of the diagonal Schwartz test by reversal of its coordinates. -/
def reverseTest (F : 𝓢(Z, ℂ)) : 𝓢(Z, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ reverseEquiv F

theorem reverseTest_apply (F : 𝓢(Z, ℂ)) (z : Z) : reverseTest F z = F (z ∘ Fin.rev) := rfl

private theorem integral_reverse (f : Z → ℂ) : (∫ z, f (z ∘ Fin.rev)) = ∫ z, f z := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℂ) Fin.revPerm
  have he (z : Z) : e z = z ∘ Fin.rev := by
    funext j
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℂ)
      Fin.revPerm z j.rev
    change e z j.rev.rev = z j.rev at h
    simpa only [Fin.rev_rev, Function.comp_apply] using h
  have hm : MeasurePreserving e (volume : Measure Z) volume :=
    volume_measurePreserving_piCongrLeft (fun _ => ℂ) Fin.revPerm
  simp_rw [← he]
  rw [← integral_map_equiv (μ := (volume : Measure Z)) e f, hm.map_eq]

private theorem normalizedZeta_reverse (F : 𝓢(Z, ℂ)) (m : W) (u : Z) :
    normalizedZeta (reverseTest F) (m ∘ Fin.rev) (u ∘ Fin.rev) = normalizedZeta F m u := by
  unfold normalizedZeta zeta
  have hg : (∏ j : Fin n, gammaNormalizer (m j.rev) (u j.rev)) =
      ∏ j : Fin n, gammaNormalizer (m j) (u j) :=
    Fintype.prod_equiv Fin.revPerm _ _ (fun _ => rfl)
  have hi (z : Z) : integrand (reverseTest F) (m ∘ Fin.rev) (u ∘ Fin.rev) z =
      integrand F m u (z ∘ Fin.rev) := by
    simp only [integrand, reverseTest_apply, Function.comp_apply]
    exact congrArg (F (z ∘ Fin.rev) * ·) (Fintype.prod_equiv Fin.revPerm _ _
      (fun j => by simp only [Fin.revPerm_apply, Fin.rev_rev]))
  simp only [Function.comp_apply, hg, hi, integral_reverse]

/-- Simultaneous reversal of the diagonal test, angular weights, and parameters leaves
the entire normalized product Tate integral unchanged. -/
def ComplexTateProductReversalStatement : Prop :=
  ∀ (H : 𝓢(Z, ℂ) → W → Z → ℂ), IsEntireNormalization H → ∀ F m u,
    H (reverseTest F) (m ∘ Fin.rev) (u ∘ Fin.rev) = H F m u

theorem complexTateProductReversal : ComplexTateProductReversalStatement (n := n) := by
  intro H hH F m u
  let c (j : Fin n) : ℝ := 1 - (u j).re
  let U := affineParameter u c
  have h₁ (j : Fin n) : (U 1 j).re = 1 := by simp [U, c, affineParameter]
  have hpos : ∀ᶠ w : ℂ in 𝓝 (1 : ℂ), ∀ j, 0 < (U w j).re := by
    apply Filter.eventually_all.mpr
    intro j
    have hc : Continuous (fun w : ℂ => (U w j).re) :=
      continuous_re.comp (continuous_const.add (continuous_const.mul continuous_id))
    exact (isOpen_lt continuous_const hc).mem_nhds (by
      change 0 < (U 1 j).re
      rw [h₁]
      exact zero_lt_one)
  have ha : AnalyticOnNhd ℂ (fun w => H (reverseTest F) (m ∘ Fin.rev) (U w ∘ Fin.rev)) univ :=
    fun w _ => (hH.1 (reverseTest F) (m ∘ Fin.rev) (u ∘ Fin.rev) (c ∘ Fin.rev)).analyticAt w
  have hb : AnalyticOnNhd ℂ (fun w => H F m (U w)) univ :=
    fun w _ => (hH.1 F m u c).analyticAt w
  have he : (fun w => H (reverseTest F) (m ∘ Fin.rev) (U w ∘ Fin.rev)) =ᶠ[𝓝 (1 : ℂ)]
      fun w => H F m (U w) := by
    filter_upwards [hpos] with w hw
    rw [hH.2 (reverseTest F) (m ∘ Fin.rev) (U w ∘ Fin.rev) (fun j => hw j.rev),
      hH.2 F m (U w) hw]
    exact normalizedZeta_reverse F m (U w)
  have hz : U 0 = u := by
    funext j
    simp [U, affineParameter]
  have h := congrFun (ha.eq_of_eventuallyEq hb he) 0
  change H (reverseTest F) (m ∘ Fin.rev) (U 0 ∘ Fin.rev) = H F m (U 0) at h
  rwa [hz] at h

end Langlands.Global.RankinSelbergGlobal.ComplexTateProduct
