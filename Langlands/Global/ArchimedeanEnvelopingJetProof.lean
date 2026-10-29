import Langlands.Global.ArchimedeanEnvelopingJetStatement
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! # Comparing the genuine enveloping jet with the ambient matrix jet -/

noncomputable section
universe u
open scoped Classical ContDiff Matrix.Norms.Operator
open Set Filter Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

private theorem iteratedFDeriv_clm_eq_zero
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set E} (hS : IsOpen S) {x : E} (hx : x ∈ S)
    {c : E → F →L[ℝ] G} (hc : ContDiffOn ℝ ∞ c S)
    (m : ℕ) (hz : ∀ v : F, iteratedFDeriv ℝ m (fun y => c y v) x = 0) :
    iteratedFDeriv ℝ m c x = 0 := by
  ext w v
  have he := iteratedFDerivWithin_clm_apply_const_apply hS.uniqueDiffOn hc
    (show (m : ℕ∞ω) ≤ ∞ by simp) hx (u := v) (m := w)
  rw [iteratedFDerivWithin_of_isOpen m hS hx,
    iteratedFDerivWithin_of_isOpen m hS hx] at he
  rw [← he, hz v]
  rfl

private theorem iteratedFDeriv_bilinear_eq_zero
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {S : Set E} (hS : IsOpen S) {x : E} (hx : x ∈ S)
    (B : F →L[ℝ] G →L[ℝ] H) {c : E → F} {d : E → G}
    (hc : ContDiffOn ℝ ∞ c S) (hd : ContDiffOn ℝ ∞ d S)
    (m : ℕ) (hz : ∀ j ≤ m, iteratedFDeriv ℝ j c x = 0) :
    iteratedFDeriv ℝ m (fun y => B (c y) (d y)) x = 0 := by
  have hb := B.norm_iteratedFDerivWithin_le_of_bilinear hc hd hS.uniqueDiffOn hx
    (show (m : ℕ∞ω) ≤ ∞ by simp)
  rw [iteratedFDerivWithin_of_isOpen m hS hx] at hb
  have hs : (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
      ‖iteratedFDerivWithin ℝ j c S x‖ *
      ‖iteratedFDerivWithin ℝ (m - j) d S x‖) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hS hx,
      hz j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), norm_zero, mul_zero, zero_mul]
  rw [hs, mul_zero] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Every genuine enveloping derivative vanishing at a point forces its full matrix jet to vanish. -/
theorem envelopingZeroJet : EnvelopingZeroJetStatement K n := by
  intro f x₀ hzero m
  let x : ArchimedeanMatrix K n :=
    (archimedeanGLCoordinates K n x₀ : ArchimedeanMatrix K n)
  let S : Set (ArchimedeanMatrix K n) :=
    Set.range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)
  have hS : IsOpen S := Units.isOpenEmbedding_val.isOpen_range
  have hx : x ∈ S := ⟨archimedeanGLCoordinates K n x₀, rfl⟩
  suffices hall : ∀ k : ℕ, ∀ a : EnvelopingAlgebra K n,
      iteratedFDeriv ℝ k (coordinateExtension K n (envelopingAction K n a f)) x = 0 by
    simpa only [envelopingAction_one] using hall m 1
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro a
    cases k with
    | zero =>
      ext v
      simpa only [iteratedFDeriv_zero_apply, zero_apply, x, coordinateExtension_apply,
        ContinuousMulEquiv.symm_apply_apply] using hzero a
    | succ r =>
      let fa := envelopingAction K n a f
      let F := coordinateExtension K n fa
      let L := ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)
      let D : ArchimedeanMatrix K n → ArchimedeanMatrix K n →L[ℝ] ℂ :=
        fun y => (fderiv ℝ F y).comp (L y)
      let T : ArchimedeanMatrix K n →
          ArchimedeanMatrix K n →L[ℝ] ArchimedeanMatrix K n :=
        fun y => L (Ring.inverse y)
      have hF : ContDiffOn ℝ ∞ F S := coordinateExtension_contDiffOn K n fa
      have hD : ContDiffOn ℝ ∞ D S :=
        (hF.fderiv_of_isOpen hS (by simp)).clm_comp L.contDiff.contDiffOn
      have hT : ContDiffOn ℝ ∞ T S := by
        rintro y ⟨g, rfl⟩
        exact (L.contDiff.contDiffAt.comp _ (contDiffAt_ringInverse ℝ g)).contDiffWithinAt
      have hDzero : ∀ j ≤ r, iteratedFDeriv ℝ j D x = 0 := by
        intro j hj
        apply iteratedFDeriv_clm_eq_zero hS hx hD j
        intro Y
        let X := (realLieAlgebraToMatrix K n).symm Y
        have heq : (fun y => D y Y) =ᶠ[𝓝 x]
            coordinateExtension K n (smoothDifferential K n X fa) := by
          filter_upwards [hS.mem_nhds hx] with y hy
          obtain ⟨g, rfl⟩ := hy
          simp only [D, L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
            coordinateExtension_apply, smoothDifferential_apply,
            ContinuousMulEquiv.apply_symm_apply, X, LinearEquiv.apply_symm_apply, F]
        rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
        have hmul : smoothDifferential K n X fa =
            envelopingAction K n
              (envelopingGenerator K n (complexify K n X) * a) f := by
          rw [envelopingAction_mul, envelopingAction_real_generator]
        rw [hmul]
        exact ih j (Nat.lt_succ_of_le hj) _
      have hcomp := iteratedFDeriv_bilinear_eq_zero hS hx
        (ContinuousLinearMap.compL ℝ (ArchimedeanMatrix K n)
          (ArchimedeanMatrix K n) ℂ) hD hT r hDzero
      have heq : (fun y => (D y).comp (T y)) =ᶠ[𝓝 x] fderiv ℝ F := by
        filter_upwards [hS.mem_nhds hx] with y hy
        obtain ⟨g, rfl⟩ := hy
        ext Y
        change fderiv ℝ F (g : ArchimedeanMatrix K n)
          ((g : ArchimedeanMatrix K n) *
            (Ring.inverse (g : ArchimedeanMatrix K n) * Y)) = _
        rw [Ring.inverse_unit, Units.mul_inv_cancel_left]
      change iteratedFDeriv ℝ (r + 1) F x = 0
      have hfzero : iteratedFDeriv ℝ r (fderiv ℝ F) x = 0 := by
        rw [← (heq.iteratedFDeriv ℝ r).eq_of_nhds]
        exact hcomp
      ext v
      rw [iteratedFDeriv_succ_apply_right, hfzero]
      rfl

end Langlands.Global.ArchimedeanGL
