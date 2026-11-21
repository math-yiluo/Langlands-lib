import Langlands.Analysis.DistributionFamilyIntegral
import Langlands.Analysis.SchwartzCompactFamilies
import Langlands.Global.RankinSelberg.TriangularDiagonal
import Langlands.Representation.Archimedean.MatrixTestFunctions
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Weighted Borel averaging of complex matrix tests -/

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.Archimedean

open Langlands.Analysis Langlands.GeneralLinear
open Langlands.Global.RankinSelbergGlobal.GaugeDescent (isClosed_upperTriangular)
open Langlands.Analysis.SchwartzCompactFamilies (contDiff_iteratedFDeriv_slice)

variable (n : ℕ)

local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "GL" => Langlands.GeneralLinear n ℂ
local notation "B" => upperTriangularSubgroup n ℂ
local notation "Ω" => matrixUnitsOpen ℂ n
local notation "Test" => 𝓓(Ω, ℂ)

/-- For compact sets of invertible matrices, the right Borel transporters
are contained in a compact subset of the actual upper triangular subgroup. -/
theorem exists_compact_complexBorel_right_transport {K L : Set Mat}
    (hK : IsCompact K) (hL : IsCompact L) (hKΩ : K ⊆ Ω) (hLΩ : L ⊆ Ω) :
    ∃ C : Set B, IsCompact C ∧ ∀ (b : B) (x : Mat), x ∈ K → x * b.val.val ∈ L → b ∈ C := by
  let v : GL → Mat := Units.val
  let Q : Set GL := (fun z : GL × GL => z.1⁻¹ * z.2) '' ((v ⁻¹' K) ×ˢ (v ⁻¹' L))
  have hlift {S : Set Mat} (hS : IsCompact S) (hSΩ : S ⊆ Ω) : IsCompact (v ⁻¹' S) := by
    apply Units.isOpenEmbedding_val.isEmbedding.isInducing.isCompact_preimage' hS
    intro x hx
    exact hSΩ hx
  have hQ : IsCompact Q :=
    ((hlift hK hKΩ).prod (hlift hL hLΩ)).image (continuous_fst.inv.mul continuous_snd)
  have hQB : IsCompact (Q ∩ (B : Set GL)) := hQ.inter_right isClosed_upperTriangular
  let C : Set B := Subtype.val ⁻¹' (Q ∩ (B : Set GL))
  refine ⟨C, Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hQB ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hx.2⟩, rfl⟩
  intro b x hx hxb
  obtain ⟨g, rfl⟩ := (show IsUnit x from hKΩ hx)
  refine ⟨⟨(g, g * b.val), ⟨hx, hxb⟩, ?_⟩, b.property⟩
  change g⁻¹ * (g * b.val) = b.val
  simp only [inv_mul_cancel_left]

private lemma smoothCompact_borelAverage_window (c : B → ℂ) (hc : Continuous c)
    (f : Test) (w : Mat → ℝ) (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w)
    (hwΩ : tsupport w ⊆ Ω) :
    SmoothCompactFamily (fun b : B => fun x : Mat => w x • (c b * f (x * b.val.val))) := by
  let H : (ℂ × Mat) × Mat → ℂ := fun z =>
    w z.2 • (z.1.1 * f (z.2 * z.1.2))
  have hH : ContDiff ℝ ∞ H := by
    exact (hw.comp contDiff_snd).smul
      ((contDiff_fst.comp contDiff_fst).mul (f.contDiff.comp (contDiff_snd.mul contDiff_fst.snd)))
  let a : B → ℂ × Mat := fun b => (c b, b.val.val)
  have ha : Continuous a := hc.prodMk (Units.continuous_val.comp continuous_subtype_val)
  obtain ⟨C, hC, hTransport⟩ :=
    exists_compact_complexBorel_right_transport n hwc f.hasCompactSupport hwΩ f.tsupport_subset
  refine ⟨fun b => ?_, fun j => ?_, ⟨C, hC, ?_⟩⟩
  · change ContDiff ℝ ∞ (H ∘ fun x : Mat => (a b, x))
    exact hH.comp (contDiff_const.prodMk contDiff_id)
  · exact (contDiff_iteratedFDeriv_slice hH j).continuous.comp
      ((ha.comp continuous_fst).prodMk continuous_snd)
  · intro b hb x
    by_cases hx : x ∈ tsupport w
    · have h : x * b.val.val ∉ tsupport f := fun h => hb (hTransport b x hx h)
      rw [image_eq_zero_of_notMem_tsupport h, mul_zero, smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

section Measure

variable [MeasurableSpace (upperTriangularSubgroup n ℂ)] [BorelSpace (upperTriangularSubgroup n ℂ)]
  (μ : Measure (upperTriangularSubgroup n ℂ)) [IsFiniteMeasureOnCompacts μ]

/-- The Borel integral of a matrix test against a continuous weight at a matrix argument. -/
def complexBorelMatrixAverage (c : B → ℂ) (f : Test) (x : Mat) : ℂ :=
  ∫ b : B, c b * f (x * b.val.val) ∂μ

theorem integrable_complexBorelMatrixAverage (c : B → ℂ) (hc : Continuous c)
    (f : Test) {x : Mat} (hx : x ∈ Ω) :
    Integrable (fun b : B => c b * f (x * b.val.val)) μ := by
  obtain ⟨C, hC, hTransport⟩ := exists_compact_complexBorel_right_transport n
    (isCompact_singleton (x := x)) f.hasCompactSupport
    (Set.singleton_subset_iff.mpr hx) f.tsupport_subset
  have hval : Continuous (fun b : B => b.val.val) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc' : Continuous (fun b : B => c b * f (x * b.val.val)) :=
    hc.mul (f.continuous.comp (continuous_const.mul hval))
  apply hc'.integrable_of_hasCompactSupport
  apply hC.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hC.isClosed
  intro b hb
  have hf : f (x * b.val.val) ≠ 0 := by
    intro h
    apply hb
    change c b * f (x * b.val.val) = 0
    rw [h, mul_zero]
  exact hTransport b x (mem_singleton x) (subset_tsupport f hf)

variable [SecondCountableTopology (upperTriangularSubgroup n ℂ)]

/-- The weighted Borel integral is smooth on the open set of invertible matrices. -/
theorem contDiffOn_complexBorelMatrixAverage (c : B → ℂ) (hc : Continuous c) (f : Test) :
    ContDiffOn ℝ ∞ (complexBorelMatrixAverage n μ c f) Ω := by
  intro x hx
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp (matrixUnitsOpen ℂ n).isOpen x hx
  let w : ContDiffBump x := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hwΩ : tsupport w ⊆ Ω := by
    rw [w.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by dsimp [w]; linarith)).trans hBall
  have hFamily := smoothCompact_borelAverage_window n c hc f w w.contDiff
    w.hasCompactSupport hwΩ
  refine ((contDiff_integral_family (μ := μ) hFamily).contDiffAt.congr_of_eventuallyEq
    ?_).contDiffWithinAt
  filter_upwards [Metric.ball_mem_nhds x w.rIn_pos] with y hy
  have hone : w y = 1 := w.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  simp only [complexBorelMatrixAverage, hone, one_smul]

variable [μ.IsMulLeftInvariant]

omit [SecondCountableTopology (upperTriangularSubgroup n ℂ)] [IsFiniteMeasureOnCompacts μ] in
/-- On inverse arguments, left Borel translation realizes the inducing character. -/
theorem complexBorelMatrixAverage_inv_mul (χ : B →* ℂ) (f : Test)
    (b₀ : B) (g : GL) :
    complexBorelMatrixAverage n μ χ f (b₀.val * g)⁻¹.val =
      χ b₀ * complexBorelMatrixAverage n μ χ f g⁻¹.val := by
  let e := (Homeomorph.mulLeft b₀).toMeasurableEquiv
  have he : MeasurePreserving e μ μ := ⟨e.measurable, map_mul_left_eq_self μ b₀⟩
  unfold complexBorelMatrixAverage
  rw [← he.integral_comp' (fun b : B => χ b * f ((b₀.val * g)⁻¹.val * b.val.val)),
    ← integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun b => ?_)
  have hprod : (b₀.val * g)⁻¹ * (b₀ * b).val = g⁻¹ * b.val := by
    simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  change χ (b₀ * b) * f (((b₀.val * g)⁻¹ * (b₀ * b).val).val) =
    χ b₀ * (χ b * f ((g⁻¹ * b.val).val))
  rw [hprod, map_mul, mul_assoc]

end Measure

end Langlands.Archimedean
