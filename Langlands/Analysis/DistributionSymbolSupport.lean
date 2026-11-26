import Langlands.Analysis.DistributionLocalVanishing

/-! # Distributional support from smooth annihilating multipliers -/

noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace Langlands.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}

/-- Multiplication of a compactly supported test by a smooth complex multiplier. -/
def multiplyTest (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (a : 𝓓(Ω, ℂ)) : 𝓓(Ω, ℂ) :=
  ⟨b * a, hb.mul a.contDiff, a.hasCompactSupport.mul_left,
    tsupport_mul_subset_right.trans a.tsupport_subset⟩

private theorem exists_dividedTest (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (a : 𝓓(Ω, ℂ))
    (hnz : ∀ x ∈ tsupport a, b x ≠ 0) :
    ∃ c : 𝓓(Ω, ℂ), multiplyTest b hb c = a := by
  let f (x : E) : ℂ := a x / b x
  have hf : ContDiff ℝ ∞ f := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport a
    · simpa only [f, div_eq_mul_inv] using
        a.contDiff.contDiffAt.mul (hb.contDiffAt.fun_inv (hnz x hx))
    · have hEq : f =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds (show x ∈ (tsupport a)ᶜ from hx)]
          with y hy
        change a y / b y = 0
        rw [image_eq_zero_of_notMem_tsupport hy, zero_div]
      exact contDiffAt_const.congr_of_eventuallyEq hEq
  have hsub : tsupport f ⊆ tsupport a := by
    simp only [f, div_eq_mul_inv]
    exact tsupport_mul_subset_left
  refine ⟨⟨f, hf, a.hasCompactSupport.of_isClosed_subset isClosed_closure hsub,
    hsub.trans a.tsupport_subset⟩, ?_⟩
  apply TestFunction.ext
  intro x
  change b x * (a x / b x) = a x
  by_cases hx : x ∈ tsupport a
  · rw [mul_comm, div_mul_cancel₀ _ (hnz x hx)]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_div, mul_zero]

/-- The support of a distribution annihilated by each of a family of smooth multipliers
lies in their common zero set. If that set is finite, the distribution has finite support
and vanishes on compactly supported smooth tests whose support avoids the common zeros. -/
def DistributionSymbolSupportStatement : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Ω : Opens E}
    {ι : Type*} (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ) (p : ι → E → ℂ) (hp : ∀ i, ContDiff ℝ ∞ (p i)),
    (∀ i (a : 𝓓(Ω, ℂ)), T (multiplyTest (p i) (hp i) a) = 0) →
    let Z := {x | ∀ i, p i x = 0}
    Distribution.dsupport T ⊆ Z ∧ Distribution.IsVanishingOn T Zᶜ ∧
      (Z.Finite → (Distribution.dsupport T).Finite)

/-- Divide a test locally by a nonvanishing symbol and use local vanishing. -/
theorem distributionSymbolSupport : DistributionSymbolSupportStatement := by
  classical
  intro E _ _ _ Ω ι T p hp hann Z
  have hOpen (i : ι) : IsOpen {x | p i x ≠ 0} :=
    (isClosed_singleton.preimage (hp i).continuous).isOpen_compl
  have hVanishing (i : ι) : Distribution.IsVanishingOn T {x | p i x ≠ 0} := by
    intro a ha
    obtain ⟨c, hc⟩ := exists_dividedTest (p i) (hp i) a (fun x hx => ha hx)
    exact hc ▸ hann i c
  have hSupport : Distribution.dsupport T ⊆ Z := by
    intro x hx i
    by_contra hnx
    exact (Distribution.notMem_dsupport_iff x).mpr
      ⟨{x | p i x ≠ 0}, hVanishing i, hOpen i, hnx⟩ hx
  refine ⟨hSupport, isVanishingOn_of_locallyVanishing T ?_, fun hZ => hZ.subset hSupport⟩
  intro x hx
  have hx' : ¬ ∀ i, p i x = 0 := hx
  obtain ⟨i, hi⟩ := not_forall.mp hx'
  exact ⟨{x | p i x ≠ 0}, hOpen i, hi, hVanishing i⟩

end Langlands.Analysis
