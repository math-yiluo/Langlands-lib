import Langlands.Analysis.Local.QuotientL2UnfoldingStatement
import Langlands.Analysis.Local.QuotientWeilKernel
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory ProbabilityTheory
open scoped CompactlySupported ProbabilityTheory

universe uG

private theorem quotientMap_subgroup_mul {G : Type uG} [Group G]
    (H : Subgroup G) (h : H) (g : G) :
    leftQuotientMap H (h.val * g) = leftQuotientMap H g := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simp [mul_inv_rev]

section FunctionUnfolding

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) (hH : IsClosed (H : Set G))
  [MeasurableSpace H] [BorelSpace H]
  (μH : Measure H) [SFinite μH] [μH.IsMulRightInvariant]
  [IsFiniteMeasureOnCompacts μH]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
  (ν : Measure (LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]

include hH in
/-- Absolute convergence and unfolding for a specified strongly measurable L²
function; this also applies to direct pullbacks of chosen L² representatives. -/
theorem integrable_compact_quotient_unfolding (hν : IsCompatible H μG μH ν)
    (f : C_c(G, ℂ)) (ψ : LeftQuotient H → ℂ)
    (hψm : StronglyMeasurable ψ) (hψ : MemLp ψ 2 ν) :
    Integrable (fun g => star (f g) * ψ (leftQuotientMap H g)) μG ∧
    (∫ g, star (f g) * ψ (leftQuotientMap H g) ∂μG) =
      ∫ q, star (quotientAverage H μH f q) * ψ q ∂ν := by
  let P : C_c(G, ℝ) → C_c(LeftQuotient H, ℝ) :=
    quotientAverageRealPositive H hH μH
  let F : G → ℂ := fun g => star (f g) * ψ (leftQuotientMap H g)
  have hproj : Measurable (leftQuotientMap H) :=
    (leftQuotient_isOpenQuotientMap H).continuous.measurable
  have hFm : StronglyMeasurable F :=
    f.continuous.stronglyMeasurable.star.mul (hψm.comp_measurable hproj)
  let κ := orbitKernel H hH μH
  have hκ : κ ∘ₘ ν = μG := orbitKernel_comp H hH μH μG ν hν
  let fN : C_c(G, ℝ) :=
    ⟨⟨fun g => ‖f g‖, f.continuous.norm⟩, f.hasCompactSupport.comp_left norm_zero⟩
  let a : C_c(LeftQuotient H, ℝ) := P fN
  have ha : MemLp a 2 ν := a.continuous.memLp_of_hasCompactSupport a.hasCompactSupport
  have hbound : Integrable (fun q => a q * ‖ψ q‖) ν :=
    ha.integrable_mul hψ.norm
  have hfiber : ∀ q, Integrable F (κ q) := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [show κ (Quotient.mk _ g) = _ from orbitKernel_mk H hH μH g]
      apply (integrable_map_measure hFm.aestronglyMeasurable
        (continuous_subtype_val.mul_const g).measurable.aemeasurable).2
      let fs : G → ℂ := fun x => star (f x)
      have hfs : Integrable (fun h : H => fs (h.val * g)) μH :=
        integrable_subgroup_mul_of_hasCompactSupport H hH μH fs f.continuous.star
          (f.hasCompactSupport.comp_left (star_zero ℂ)) g
      simpa only [Function.comp_def, F, fs, quotientMap_subgroup_mul] using
        hfs.mul_const (ψ (leftQuotientMap H g))
  have hnorm : ∀ q, (∫ g, ‖F g‖ ∂κ q) = a q * ‖ψ q‖ := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [show κ (Quotient.mk _ g) = _ from orbitKernel_mk H hH μH g,
        integral_map_of_stronglyMeasurable
          (continuous_subtype_val.mul_const g).measurable hFm.norm]
      simp only [F, quotientMap_subgroup_mul, norm_mul, norm_star]
      rw [integral_mul_const]
      rfl
  have hFcomp : Integrable F (κ ∘ₘ ν) := by
    apply (Measure.integrable_comp_iff hFm.aestronglyMeasurable).2
    exact ⟨Filter.Eventually.of_forall hfiber, hbound.congr
      (Filter.Eventually.of_forall fun q => (hnorm q).symm)⟩
  have hF : Integrable F μG := hκ ▸ hFcomp
  have hiter : (∫ g, F g ∂μG) = ∫ q, ∫ g, F g ∂κ q ∂ν := by
    rw [← hκ, Measure.comp_eq_comp_const_apply] at hF ⊢
    simpa only [Kernel.const_apply] using Kernel.integral_comp hF
  have hinnerfiber : ∀ q, (∫ g, F g ∂κ q) = star (quotientAverage H μH f q) * ψ q := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [show κ (Quotient.mk _ g) = _ from orbitKernel_mk H hH μH g,
        integral_map_of_stronglyMeasurable
          (continuous_subtype_val.mul_const g).measurable hFm]
      simp only [F, quotientMap_subgroup_mul, integral_mul_const, quotientAverage_mk]
      congr 1
      exact integral_conj
  refine ⟨hF, hiter.trans ?_⟩
  exact integral_congr_ae (Filter.Eventually.of_forall hinnerfiber)

end FunctionUnfolding

/-- The exact compact averaging and absolutely convergent unfolding target. -/
theorem quotientL2Unfolding : QuotientL2UnfoldingStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ H hH _ _ μH _ _ _ _ _ μG _ ν _ hν f
  let P : C_c(G, ℝ) → C_c(LeftQuotient H, ℝ) :=
    quotientAverageRealPositive H hH μH
  let C : C_c(LeftQuotient H, ℂ) := complexifyCompactMap P f
  have hC : (C : LeftQuotient H → ℂ) = quotientAverage H μH f :=
    complexifyCompactMap_eq_quotientAverage H μH P (by intros; rfl) f
      (integrable_subgroup_mul_of_hasCompactSupport H hH μH f
        f.continuous f.hasCompactSupport)
  have hcont : Continuous (quotientAverage H μH f) := by
    rw [← hC]
    exact C.continuous
  have hcompact : HasCompactSupport (quotientAverage H μH f) := by
    rw [← hC]
    exact C.hasCompactSupport
  have hLp : MemLp (quotientAverage H μH f) 2 ν :=
    hcont.memLp_of_hasCompactSupport hcompact
  let v : Lp ℂ 2 ν := hLp.toLp (quotientAverage H μH f)
  have hv : (v : LeftQuotient H → ℂ) =ᵐ[ν] quotientAverage H μH f := hLp.coeFn_toLp
  refine ⟨hcont, hcompact, v, innerSL ℂ v, hv, ?_⟩
  intro φ
  obtain ⟨hF, hunfold⟩ := integrable_compact_quotient_unfolding H hH μH μG ν hν f φ
    (Lp.stronglyMeasurable φ) (Lp.memLp φ)
  refine ⟨hF, innerSL_apply_apply ℂ v φ, ?_⟩
  calc
    inner ℂ v φ = ∫ q, star (quotientAverage H μH f q) * φ q ∂ν := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hv] with q hq
      simp only [hq, RCLike.inner_apply', starRingEnd_apply]
    _ = _ := hunfold.symm

end Langlands.QuotientIntegration
