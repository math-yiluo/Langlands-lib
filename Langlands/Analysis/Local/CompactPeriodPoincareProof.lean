import Langlands.Analysis.Local.CompactPeriodPoincareStatement
import Mathlib.Topology.UrysohnsLemma

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory Set
open scoped CompactlySupported Pointwise

universe uG uX

/-- The exact compact-domain periodization and absolute Fubini target. -/
theorem compactPeriodPoincare : CompactPeriodPoincareStatement.{uG, uX} := by
  intro G _ _ _ _ _ _ _ _ Γ hΓ _ _ μΓ _ _ _ X _ _ _ _ _ _ μ _ s hs hsc j hj w hw f
  let : IsClosed (Γ : Set G) := hΓ
  have hμs : μ s < ⊤ := (measure_mono subset_closure).trans_lt hsc.measure_lt_top
  let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hμs⟩
  obtain ⟨ρ, hρ1, -, hρcs, -⟩ :=
    exists_continuous_one_zero_of_isCompact hsc isClosed_empty (Set.disjoint_empty _)
  let W : X → ℂ := fun x => w x * (ρ x : ℂ)
  have hWcont : Continuous W := hw.mul (Complex.continuous_ofReal.comp ρ.continuous)
  have hWcs : HasCompactSupport W :=
    (hρcs.comp_left Complex.ofReal_zero).mul_left
  have hWeq : ∀ x ∈ s, W x = w x := by
    intro x hx
    simp only [W, hρ1 (subset_closure hx), Pi.one_apply, Complex.ofReal_one, mul_one]
  have hint : ∀ g, Integrable
      (fun p : Γ × X => w p.2 * f ((j p.2)⁻¹ * (p.1.val * g)))
      (μΓ.prod (μ.restrict s)) := by
    intro g
    let L : Set Γ :=
      Subtype.val ⁻¹' (((j '' tsupport W) * tsupport f) * {g⁻¹})
    have hL : IsCompact L :=
      hΓ.isClosedEmbedding_subtypeVal.isCompact_preimage
        (((hWcs.image hj).mul f.hasCompactSupport).mul isCompact_singleton)
    let J : Γ × X → ℂ := fun p => W p.2 * f ((j p.2)⁻¹ * (p.1.val * g))
    have hJcont : Continuous J :=
      (hWcont.comp continuous_snd).mul (f.continuous.comp
        ((hj.comp continuous_snd).inv.mul
          ((continuous_subtype_val.comp continuous_fst).mul_const g)))
    have hsupp : Function.support J ⊆ L ×ˢ tsupport W := by
      intro p hp
      have hne : W p.2 ≠ 0 ∧ f ((j p.2)⁻¹ * (p.1.val * g)) ≠ 0 :=
        mul_ne_zero_iff.mp hp
      have hx : p.2 ∈ tsupport W := subset_tsupport W hne.1
      have hf : (j p.2)⁻¹ * (p.1.val * g) ∈ tsupport f := subset_tsupport f hne.2
      refine ⟨?_, hx⟩
      change p.1.val ∈ ((j '' tsupport W) * tsupport f) * {g⁻¹}
      exact ⟨j p.2 * ((j p.2)⁻¹ * (p.1.val * g)),
        ⟨j p.2, ⟨p.2, hx, rfl⟩, (j p.2)⁻¹ * (p.1.val * g), hf, rfl⟩,
        g⁻¹, by simp, by simp⟩
    have hJcs : HasCompactSupport J :=
      (hL.prod hWcs).of_isClosed_subset (isClosed_tsupport J)
        (closure_minimal hsupp (hL.prod hWcs).isClosed)
    have hJint : Integrable J (μΓ.prod (μ.restrict s)) :=
      hJcont.integrable_of_hasCompactSupport hJcs
    apply hJint.congr
    have hx : ∀ᵐ p : Γ × X ∂μΓ.prod (μ.restrict s), p.2 ∈ s :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hs)
    filter_upwards [hx] with p hp
    simp only [J, hWeq p.2 hp]
  refine ⟨hint, ?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [quotientAverage_mk]
    calc
      _ = ∫ x in s, ∫ γ : Γ, w x * f ((j x)⁻¹ * (γ.val * g)) ∂μΓ ∂μ :=
        integral_integral_swap (hint g)
      _ = _ := by simp only [integral_const_mul]

end Langlands.QuotientIntegration
