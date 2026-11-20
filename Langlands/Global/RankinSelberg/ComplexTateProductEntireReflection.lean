import Langlands.Global.RankinSelberg.ComplexTateProductContinuation
import Langlands.Global.RankinSelberg.ComplexTateProductFullFourier

/-! # Entire normalized product Tate reflection -/

noncomputable section

open Complex Filter Set
open scoped SchwartzMap Topology

namespace Langlands.Global.RankinSelbergGlobal.ComplexTateProduct

set_option autoImplicit false

/-- Every full positive trace Fourier reflection holds at all spectral parameters for
the entire normalization. -/
def ComplexTateProductEntireReflectionStatement : Prop :=
  ∀ (n : ℕ) (H : 𝓢(Fin (n + 1) → ℂ, ℂ) → (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℂ) → ℂ),
    IsEntireNormalization H → ∀ F m u,
    H (ComplexTraceFourier.transform (-1) F) (fun j => -m j) (fun j => 1 - u j) =
      (∏ j, I ^ (m j).natAbs) * H F m u

theorem complexTateProductEntireReflection : ComplexTateProductEntireReflectionStatement := by
  intro n H hH F m u
  let c (j : Fin (n + 1)) : ℝ := 1 / 2 - (u j).re
  let U := affineParameter u c
  let G := ComplexTraceFourier.transform (-1) F
  let phase : ℂ := ∏ j, I ^ (m j).natAbs
  have hr (w : ℂ) : (fun j => 1 - U w j) =
      affineParameter (fun j => 1 - u j) (fun j => -c j) w := by
    funext j
    simp only [U, affineParameter, ofReal_neg]
    ring
  have h₁ (j : Fin (n + 1)) : (U 1 j).re = 1 / 2 := by
    simp [U, c, affineParameter]
  have hevent :
      ∀ᶠ w : ℂ in 𝓝 (1 : ℂ), ∀ j, 0 < (U w j).re ∧ (U w j).re < 1 := by
    apply Filter.eventually_all.mpr
    intro j
    have hc : Continuous (fun w : ℂ => (U w j).re) :=
      continuous_re.comp (continuous_const.add (continuous_const.mul continuous_id))
    have hpos : ∀ᶠ w in 𝓝 (1 : ℂ), 0 < (U w j).re :=
      (isOpen_lt continuous_const hc).mem_nhds (by
        change 0 < (U 1 j).re
        rw [h₁]
        norm_num)
    have hlt : ∀ᶠ w in 𝓝 (1 : ℂ), (U w j).re < 1 :=
      (isOpen_lt hc continuous_const).mem_nhds (by
        change (U 1 j).re < 1
        rw [h₁]
        norm_num)
    exact hpos.and hlt
  have ha : AnalyticOnNhd ℂ (fun w => H G (fun j => -m j) (fun j => 1 - U w j)) univ := by
    intro w _
    simp only [hr]
    exact (hH.1 G (fun j => -m j) (fun j => 1 - u j) (fun j => -c j)).analyticAt w
  have hb : AnalyticOnNhd ℂ (fun w => phase * H F m (U w)) univ :=
    fun w _ => analyticAt_const.mul ((hH.1 F m u c).analyticAt w)
  have he :
      (fun w => H G (fun j => -m j) (fun j => 1 - U w j)) =ᶠ[𝓝 (1 : ℂ)]
        fun w => phase * H F m (U w) := by
    filter_upwards [hevent] with w hw
    have hdual (j : Fin (n + 1)) : 0 < (1 - U w j).re := by
      simpa only [sub_re, one_re] using sub_pos.mpr (hw j).2
    rw [hH.2 G _ _ hdual, hH.2 F _ _ (fun j => (hw j).1)]
    exact complexTateProductFullFourier n F m (U w) (fun j => (hw j).1) (fun j => (hw j).2)
  have hzero : U 0 = u := by
    funext j
    simp [U, affineParameter]
  have h := congrFun (ha.eq_of_eventuallyEq hb he) 0
  change H G (fun j => -m j) (fun j => 1 - U 0 j) = phase * H F m (U 0) at h
  rwa [hzero] at h

end Langlands.Global.RankinSelbergGlobal.ComplexTateProduct
