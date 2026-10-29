import Langlands.Global.ArchimedeanCartanSymbol
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Order.Compact

/-! # Analytic coefficients and local bounds for the actual Cartan covector form -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator
open Set Filter Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The actual Cartan sum of squares, extended to all ambient matrices and continuous covectors. -/
def ambientCartanCovectorForm (y : ArchimedeanMatrix K n)
    (ℓ : ArchimedeanMatrix K n →L[ℝ] ℝ) : ℝ :=
  ∑ i : CartanBasisIndex K n,
    (ℓ (y * realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i))) ^ 2

theorem ambientCartanCovectorForm_unit (g : ArchimedeanGL K n)
    (ℓ : ArchimedeanMatrix K n →L[ℝ] ℝ) :
    ambientCartanCovectorForm K n (g : ArchimedeanMatrix K n) ℓ =
      cartanCovectorForm K n g ℓ.toLinearMap := by
  rw [cartanCovectorForm_apply]
  rfl

theorem ambientCartanCovectorForm_nonneg (y : ArchimedeanMatrix K n)
    (ℓ : ArchimedeanMatrix K n →L[ℝ] ℝ) :
    0 ≤ ambientCartanCovectorForm K n y ℓ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

@[simp]
theorem ambientCartanCovectorForm_zero (y : ArchimedeanMatrix K n) :
    ambientCartanCovectorForm K n y 0 = 0 := by
  simp [ambientCartanCovectorForm]

theorem ambientCartanCovectorForm_smul (y : ArchimedeanMatrix K n) (c : ℝ)
    (ℓ : ArchimedeanMatrix K n →L[ℝ] ℝ) :
    ambientCartanCovectorForm K n y (c • ℓ) =
      c ^ 2 * ambientCartanCovectorForm K n y ℓ := by
  simp only [ambientCartanCovectorForm, smul_apply, smul_eq_mul,
    mul_pow, Finset.mul_sum]

/-- The coefficient expression is jointly continuous with the original dual operator norm. -/
theorem continuous_ambientCartanCovectorForm :
    Continuous (fun z : ArchimedeanMatrix K n × (ArchimedeanMatrix K n →L[ℝ] ℝ) =>
      ambientCartanCovectorForm K n z.1 z.2) := by
  apply continuous_finsetSum
  intro i _
  exact (continuous_snd.clm_apply (continuous_fst.mul_const _)).pow 2

/-- For a fixed real covector the coefficients are real analytic on the whole ambient space. -/
theorem analyticAt_ambientCartanCovectorForm
    (ℓ : ArchimedeanMatrix K n →L[ℝ] ℝ) (y : ArchimedeanMatrix K n) :
    AnalyticAt ℝ (fun z => ambientCartanCovectorForm K n z ℓ) y := by
  unfold ambientCartanCovectorForm
  apply Finset.analyticAt_fun_sum
  intro i _
  exact ((ℓ.comp ((ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)).flip
    (realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i)))).analyticAt y).pow 2

theorem analyticOnNhd_ambientCartanCovectorForm (ℓ : ArchimedeanMatrix K n →L[ℝ] ℝ) :
    AnalyticOnNhd ℝ (fun z => ambientCartanCovectorForm K n z ℓ) Set.univ :=
  fun y _ => analyticAt_ambientCartanCovectorForm K n ℓ y

theorem ambientCartanCovectorForm_unit_pos (g : ArchimedeanGL K n)
    (ℓ : ArchimedeanMatrix K n →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    0 < ambientCartanCovectorForm K n (g : ArchimedeanMatrix K n) ℓ := by
  rw [ambientCartanCovectorForm_unit]
  apply cartanCovectorForm_pos
  intro h
  apply hℓ
  ext v
  exact LinearMap.congr_fun h v

/-- At every unit the actual dual norm has a uniform positive quadratic bound on an open
ambient neighborhood. The constant and neighborhood precede every covector. -/
theorem ambientCartanCovectorForm_local_bound (g : ArchimedeanGL K n) :
    ∃ c : ℝ, 0 < c ∧ ∃ U : Set (ArchimedeanMatrix K n), IsOpen U ∧
      (g : ArchimedeanMatrix K n) ∈ U ∧
      U ⊆ Set.range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n) ∧
      ∀ y ∈ U, ∀ ℓ : ArchimedeanMatrix K n →L[ℝ] ℝ,
        c * ‖ℓ‖ ^ 2 ≤ ambientCartanCovectorForm K n y ℓ := by
  let S : Set (ArchimedeanMatrix K n →L[ℝ] ℝ) := Metric.sphere 0 1
  have hS : IsCompact S := isCompact_sphere _ _
  have hcont : Continuous (fun ℓ : ArchimedeanMatrix K n →L[ℝ] ℝ =>
      ambientCartanCovectorForm K n (g : ArchimedeanMatrix K n) ℓ) :=
    (continuous_ambientCartanCovectorForm K n).comp
      (continuous_const.prodMk continuous_id)
  obtain ⟨b, hb, hbound⟩ := hS.exists_forall_le' hcont.continuousOn
    (a := (0 : ℝ)) (by
      intro ℓ hℓ
      apply ambientCartanCovectorForm_unit_pos
      intro hz
      simp [S, hz] at hℓ)
  have hevent : ∀ᶠ y : ArchimedeanMatrix K n in 𝓝 (g : ArchimedeanMatrix K n),
      ∀ ℓ ∈ S, b / 2 < ambientCartanCovectorForm K n y ℓ := by
    apply hS.eventually_forall_of_forall_eventually
    intro ℓ hℓ
    apply continuousAt_const.eventually_lt
      (continuous_ambientCartanCovectorForm K n).continuousAt
    have := hbound ℓ hℓ
    linarith
  let V : Set (ArchimedeanMatrix K n) :=
    Set.range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)
  have hV : IsOpen V := Units.isOpenEmbedding_val.isOpen_range
  have hgV : (g : ArchimedeanMatrix K n) ∈ V := ⟨g, rfl⟩
  obtain ⟨U, hU, hUopen, hgU⟩ := mem_nhds_iff.mp
    (hevent.and (hV.mem_nhds hgV))
  refine ⟨b / 2, by linarith, U, hUopen, hgU, ?_, ?_⟩
  · exact fun y hy => (hU hy).2
  · intro y hy ℓ
    by_cases hℓ : ℓ = 0
    · simp [hℓ]
    have hn : NormedSpace.normalize ℓ ∈ S := by
      simpa [S] using NormedSpace.norm_normalize hℓ
    have hq := ((hU hy).1 (NormedSpace.normalize ℓ) hn).le
    have heq : ambientCartanCovectorForm K n y ℓ =
        ‖ℓ‖ ^ 2 * ambientCartanCovectorForm K n y (NormedSpace.normalize ℓ) := by
      simpa only [NormedSpace.norm_smul_normalize] using
        ambientCartanCovectorForm_smul K n y ‖ℓ‖ (NormedSpace.normalize ℓ)
    calc
      b / 2 * ‖ℓ‖ ^ 2 = ‖ℓ‖ ^ 2 * (b / 2) := mul_comm _ _
      _ ≤ ‖ℓ‖ ^ 2 * ambientCartanCovectorForm K n y (NormedSpace.normalize ℓ) :=
        mul_le_mul_of_nonneg_left hq (sq_nonneg _)
      _ = ambientCartanCovectorForm K n y ℓ := heq.symm

/-- The same local bound for the published form at every actual unit of the neighborhood. -/
theorem cartanCovectorForm_local_bound (g : ArchimedeanGL K n) :
    ∃ c : ℝ, 0 < c ∧ ∃ U : Set (ArchimedeanMatrix K n), IsOpen U ∧
      (g : ArchimedeanMatrix K n) ∈ U ∧
      U ⊆ Set.range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n) ∧
      ∀ h : ArchimedeanGL K n, (h : ArchimedeanMatrix K n) ∈ U →
        ∀ ℓ : ArchimedeanMatrix K n →L[ℝ] ℝ,
          c * ‖ℓ‖ ^ 2 ≤ cartanCovectorForm K n h ℓ.toLinearMap := by
  obtain ⟨c, hc, U, hUopen, hgU, hUunits, hbound⟩ := ambientCartanCovectorForm_local_bound K n g
  refine ⟨c, hc, U, hUopen, hgU, hUunits, fun h hh ℓ => ?_⟩
  rw [← ambientCartanCovectorForm_unit]
  exact hbound _ hh ℓ

/-- The covector norm is the operator norm for the matrix norm below. -/
example (ℓ : ArchimedeanMatrix K n →L[ℝ] ℝ) :
    ‖ℓ‖ = sInf {c | 0 ≤ c ∧ ∀ A : ArchimedeanMatrix K n, ‖ℓ A‖ ≤ c * ‖A‖} :=
  ContinuousLinearMap.norm_def ℓ

/-- The matrix norm is the published `L∞` operator norm over the mixed space. -/
example (A : ArchimedeanMatrix K n) :
    ‖A‖ = ((Finset.univ : Finset (Fin n)).sup fun i => ∑ j, ‖A i j‖₊ : NNReal) :=
  Matrix.linfty_opNorm_def A

end Langlands.Global.ArchimedeanGL
