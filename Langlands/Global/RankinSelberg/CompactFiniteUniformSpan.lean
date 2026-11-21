import Langlands.Global.RankinSelberg.ComplexLocalCompactProjection
import Langlands.Global.RankinSelberg.ComplexLocalCompactWeight
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Uniform approximation in a compact-finite translation-invariant space -/

noncomputable section

open Filter MeasureTheory
open scoped Topology

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

private def rightOrbit (f : K → ℂ) (k : K) (x : K) : ℂ := f (x * k)

private def compactConvolution (μ : Measure K) (w f : K → ℂ) (x : K) : ℂ :=
  ∫ k, w k * f (x * k) ∂μ

private theorem compactConvolution_mem_rightOrbit (μ : Measure K) [IsFiniteMeasure μ]
    {w f : K → ℂ} (hw : Continuous w) (hf : Continuous f)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (rightOrbit f)))) :
    compactConvolution μ w f ∈ Submodule.span ℂ (Set.range (rightOrbit f)) := by
  let V := Submodule.span ℂ (Set.range (rightOrbit f))
  let : FiniteDimensional ℂ V := hfin
  let b := Module.finBasis ℂ V
  let v (k : K) : V := ⟨rightOrbit f k, Submodule.subset_span ⟨k, rfl⟩⟩
  let c j k := b.coord j (v k)
  have hc (j : Fin (Module.finrank ℂ V)) : Continuous (c j) := by
    obtain ⟨a, ha⟩ := linearForm_eq_finitelyManyEvaluations V.subtype Subtype.val_injective (b.coord j)
    have h (k : K) : c j k = ∑ x ∈ a.support, a x * f (x * k) := ha (v k)
    rw [funext h]
    exact continuous_finsetSum _ fun x _ =>
      continuous_const.mul (hf.comp (continuous_const.mul continuous_id))
  let F : V := ∑ j, (∫ k, w k * c j k ∂μ) • b j
  have hF (x : K) : F.val x = compactConvolution μ w f x := by
    have hsum (k : K) : f (x * k) = ∑ j, c j k * (b j).val x := by
      have h := congrArg (fun u : V => u.val x) (b.sum_repr (v k))
      simpa only [v, rightOrbit, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply, c] using h.symm
    simp only [F, compactConvolution, hsum, Finset.mul_sum, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [← mul_assoc, integral_mul_const]
    · intro j _
      exact (hw.mul ((hc j).mul continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [← funext hF]
  exact F.2

private theorem compactConvolution_mem_rangeSpan (μ : Measure K) [IsFiniteMeasure μ]
    [μ.IsHaarMeasure] {w g : K → ℂ}
    {l : ℕ} (α β : Fin l → K → ℂ) (hβ : ∀ j, Continuous (β j))
    (hExp : ∀ x k, w (x⁻¹ * k) = ∑ j, α j x * β j k) (hg : Continuous g) :
    compactConvolution μ w g ∈ Submodule.span ℂ (Set.range α) := by
  have hS : compactConvolution μ w g =
      ∑ j, (∫ k, β j k * g k ∂μ) • α j := by
    funext x
    unfold compactConvolution
    have hchange : (∫ k, w k * g (x * k) ∂μ) = ∫ k, w (x⁻¹ * k) * g k ∂μ := by
      rw [← integral_mul_left_eq_self (fun k => w (x⁻¹ * k) * g k) x]
      simp only [inv_mul_cancel_left]
    rw [hchange]
    simp_rw [hExp, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum]
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, integral_const_mul]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    · intro j _
      exact ((continuous_const.mul ((hβ j).mul hg))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [hS]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self j))

/-- A compact-finite function uniformly approximable by continuous compact-finite
vectors in a right-translation-invariant space already belongs to that space. -/
def CompactFiniteUniformSpanStatement : Prop :=
  ∀ (μ : Measure K) [IsFiniteMeasure μ] [μ.IsHaarMeasure]
    (S : Submodule ℂ (K → ℂ)),
    (∀ g ∈ S, Continuous g) →
    (∀ g ∈ S, ∀ k, (fun x => g (x * k)) ∈ S) →
    (∀ g ∈ S, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => g (x * k)))) →
    ∀ f : K → ℂ, Continuous f →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * k))) →
      (∀ ε : ℝ, 0 < ε → ∃ g ∈ S, ∀ x, ‖f x - g x‖ ≤ ε) → f ∈ S

theorem compactFiniteUniformSpan : CompactFiniteUniformSpanStatement (K := K) := by
  intro μ _ _ S hS hshift hfinite f hf hff hApprox
  obtain ⟨w, hw, hwfin, hrep⟩ := exists_compactWeight_of_finite_orbit μ (rightOrbit f)
    (fun x => hf.comp (continuous_const.mul continuous_id)) hff
    (fun h x => ⟨1, x * h⁻¹, fun k => by simp [rightOrbit, mul_assoc]⟩)
  obtain ⟨l, α, β, hβ, hExp⟩ := hasFiniteCompactConvolutionKernel_of_finite_translates w hw hwfin
  let V := S ⊓ Submodule.span ℂ (Set.range α)
  let : FiniteDimensional ℂ (Submodule.span ℂ (Set.range α)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range α)
  let : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_right
  let P := compactConvolution μ w
  have hPf (x : K) : P f x = f x := by
    simpa only [P, compactConvolution, rightOrbit, mul_one] using hrep x
  have hPmem (g : K → ℂ) (hg : g ∈ S) : P g ∈ V := by
    refine ⟨?_, compactConvolution_mem_rangeSpan μ α β hβ hExp (hS g hg)⟩
    have hle : Submodule.span ℂ (Set.range (rightOrbit g)) ≤ S :=
      Submodule.span_le.mpr (fun _ ⟨k, hk⟩ => hk ▸ hshift g hg k)
    exact hle (compactConvolution_mem_rightOrbit μ hw (hS g hg) (hfinite g hg))
  let δ (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  choose g hg hErr using fun n => hApprox (δ n) (hδ n)
  let C := ∫ k, ‖w k‖ ∂μ
  have hC : Integrable (fun k => ‖w k‖) μ :=
    hw.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPbound (n : ℕ) (x : K) : ‖P (g n) x - f x‖ ≤ δ n * C := by
    rw [← hPf x]
    let J (v : K → ℂ) (k : K) := w k * v (x * k)
    have hJ (v : K → ℂ) (hv : Continuous v) : Integrable (J v) μ :=
      (hw.mul (hv.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    change ‖(∫ k, J (g n) k ∂μ) - ∫ k, J f k ∂μ‖ ≤ δ n * C
    rw [← integral_sub (hJ (g n) (hS _ (hg n))) (hJ f hf)]
    refine (norm_integral_le_integral_norm _).trans ?_
    dsimp only [C]
    rw [← integral_const_mul]
    apply integral_mono ((hJ (g n) (hS _ (hg n))).sub (hJ f hf)).norm (hC.const_mul _)
    intro k
    change ‖w k * g n (x * k) - w k * f (x * k)‖ ≤ δ n * ‖w k‖
    rw [← mul_sub, norm_mul, norm_sub_rev, mul_comm (δ n)]
    exact mul_le_mul_of_nonneg_left (hErr n (x * k)) (norm_nonneg _)
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun n => P (g n)) atTop (𝓝 f) := by
    apply tendsto_pi_nhds.mpr
    intro x
    have ht : Tendsto (fun n => ‖P (g n) x - f x‖) atTop (𝓝 0) :=
      squeeze_zero (fun _ => norm_nonneg _) (fun n => hPbound n x)
        (by simpa only [zero_mul] using hδlim.mul_const C)
    simpa only [sub_add_cancel, zero_add] using
      (tendsto_zero_iff_norm_tendsto_zero.mpr ht).add_const (f x)
  exact (V.closed_of_finiteDimensional.mem_of_tendsto hlim
    (Eventually.of_forall fun n => hPmem (g n) (hg n))).1

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
