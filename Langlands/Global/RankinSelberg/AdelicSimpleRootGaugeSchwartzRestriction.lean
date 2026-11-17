import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugePaddedIntegrand
import Mathlib.Analysis.Distribution.TemperateGrowth

/-! # Restriction of Schwartz–Bruhat functions to fixed-tail coordinate subspaces -/

noncomputable section
universe u v
open NumberField
open scoped Classical RestrictedProduct
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace GaugeCoordinateRestriction

/-- Zero extension as a continuous real linear map between finite products. -/
def extendByZeroCLM {A : Type v} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (m n : ℕ) : (Fin m → A) →L[ℝ] (Fin n → A) :=
  ContinuousLinearMap.pi fun i =>
    if hi : (i : ℕ) < m then ContinuousLinearMap.proj (⟨i, hi⟩ : Fin m) else 0

/-- Extension by ones is an affine map and has temperate growth. -/
theorem hasTemperateGrowth_extendByOne {A : Type v} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [One A] (m n : ℕ) :
    Function.HasTemperateGrowth (@extendByOne A _ m n) := by
  have he : (@extendByOne A _ m n) =
      fun x => extendByZeroCLM m n x + extendByOne (0 : Fin m → A) := by
    funext x i
    by_cases hi : (i : ℕ) < m <;>
      simp [extendByOne, extendByZeroCLM, hi]
  rw [he]
  exact (extendByZeroCLM (A := A) m n).hasTemperateGrowth.add
    (Function.HasTemperateGrowth.const _)

/-- The norm cannot decrease when every source coordinate is retained. -/
theorem norm_le_norm_extendByOne {A : Type v} [NormedAddCommGroup A] [One A]
    {m n : ℕ} (h : m ≤ n) (x : Fin m → A) : ‖x‖ ≤ ‖extendByOne (n := n) x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  rw [← extendByOne_castLE h x i]
  exact norm_le_pi_norm _ _

/-- Restrict a Schwartz function to the affine coordinate subspace with tail equal to one. -/
def restrictSchwartz {A : Type v} [NormedAddCommGroup A] [NormedSpace ℝ A] [One A]
    {m n : ℕ} (h : m ≤ n) :
    SchwartzMap (Fin n → A) ℂ →L[ℂ] SchwartzMap (Fin m → A) ℂ :=
  SchwartzMap.compCLM ℂ (hasTemperateGrowth_extendByOne m n) ⟨1, 1, fun x => by
    simpa only [pow_one, one_mul] using
      (norm_le_norm_extendByOne h x).trans (le_add_of_nonneg_left zero_le_one)⟩

@[simp]
theorem restrictSchwartz_apply {A : Type v} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [One A] {m n : ℕ} (h : m ≤ n) (Φ : SchwartzMap (Fin n → A) ℂ) (x : Fin m → A) :
    restrictSchwartz h Φ x = Φ (extendByOne x) := rfl

end GaugeCoordinateRestriction

variable (F : Type u) [Field F] [NumberField F]

local instance finiteAdelesT2 : T2Space (FiniteAdeles F) :=
  inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
    [FiniteCompletion F v, v.adicCompletionIntegers F]))

theorem archimedeanCoordinates_gaugeExtendRootRow {m n : ℕ} (x : RowVector F m) :
    archimedeanCoordinates F n (gaugeExtendRootRow F x) =
      GaugeCoordinateRestriction.extendByOne (archimedeanCoordinates F m x) := by
  funext i
  by_cases hi : (i : ℕ) < m
  · simp [archimedeanCoordinates, gaugeExtendRootRow, GaugeCoordinateRestriction.extendByOne, hi]
  · simp only [archimedeanCoordinates, gaugeExtendRootRow,
      GaugeCoordinateRestriction.extendByOne, dite_eq_right hi]
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (1 : InfiniteAdeles F) = 1
    exact map_one _

theorem finiteCoordinates_gaugeExtendRootRow {m n : ℕ} (x : RowVector F m) :
    finiteCoordinates F n (gaugeExtendRootRow F x) =
      GaugeCoordinateRestriction.extendByOne (finiteCoordinates F m x) := by
  funext i
  by_cases hi : (i : ℕ) < m
  · simp [finiteCoordinates, gaugeExtendRootRow, GaugeCoordinateRestriction.extendByOne, hi]
  · simp only [finiteCoordinates, gaugeExtendRootRow,
      GaugeCoordinateRestriction.extendByOne, dite_eq_right hi]
    rfl

/-- Pure Schwartz–Bruhat functions restrict to pure Schwartz–Bruhat functions. -/
theorem IsPureSchwartzBruhat.comp_gaugeExtendRootRow {m n : ℕ} (h : m ≤ n)
    {Φ : RowVector F n → ℂ} (hΦ : IsPureSchwartzBruhat F n Φ) :
    IsPureSchwartzBruhat F m (Φ ∘ gaugeExtendRootRow F) := by
  obtain ⟨Φinf, Φfin, hlc, hc, rfl⟩ := hΦ
  refine ⟨GaugeCoordinateRestriction.restrictSchwartz h Φinf,
    Φfin ∘ GaugeCoordinateRestriction.extendByOne,
    hlc.comp_continuous (GaugeCoordinateRestriction.continuous_extendByOne m n),
    hc.comp_isClosedEmbedding (GaugeCoordinateRestriction.isClosedEmbedding_extendByOne h), ?_⟩
  funext x
  simp only [Function.comp_apply, GaugeCoordinateRestriction.restrictSchwartz_apply,
    archimedeanCoordinates_gaugeExtendRootRow, finiteCoordinates_gaugeExtendRootRow]

/-- Fixing all remaining coordinates at one preserves the adelic Schwartz–Bruhat space. -/
theorem schwartzBruhat_comp_gaugeExtendRootRow {m n : ℕ} (h : m ≤ n)
    {Φ : RowVector F n → ℂ} (hΦ : Φ ∈ schwartzBruhat F n) :
    Φ ∘ gaugeExtendRootRow F ∈ schwartzBruhat F m := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ => exact Submodule.subset_span (hΦ.comp_gaugeExtendRootRow F h)
  | zero => exact (schwartzBruhat F m).zero_mem
  | add Φ Ψ _ _ hΦ hΨ => exact (schwartzBruhat F m).add_mem hΦ hΨ
  | smul c Φ _ hΦ => exact (schwartzBruhat F m).smul_mem c hΦ

end Langlands.Global.RankinSelbergGlobal
