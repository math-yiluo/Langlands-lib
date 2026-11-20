import Langlands.Global.LeftCosetFundamentalDomain

/-! # Local integration in a discrete left coset quotient -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

open MeasureTheory Set
open scoped ENNReal

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
  (ν : Measure H) [ν.IsMulLeftInvariant]

/-- On a measurable patch on which the quotient map is injective, the
ambient integral of a quotient function is controlled by its integral on
the quotient. If the patch maps into `A`, use the quotient measure on `A`. -/
theorem lintegral_restrict_le_discreteQuotientMeasure
    (t : Set H) (ht : MeasurableSet t) (hinj : t.InjOn (mk Γ))
    (A : Set (Langlands.Global.LeftCosetSpace Γ)) (hA : MeasurableSet A)
    (hmap : MapsTo (mk Γ) t A)
    (f : Langlands.Global.LeftCosetSpace Γ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x in t, f (mk Γ x) ∂ν ≤
      ∫⁻ q in A, f q ∂discreteQuotientMeasure Γ hΓ ν := by
  classical
  let : Countable Γ := countable_of_isDiscrete Γ hΓ
  let s := fundamentalDomain Γ hΓ
  let k : H → ℝ≥0∞ := t.indicator (fun x => f (mk Γ x))
  have hk : Measurable k := (hf.comp (measurable_mk Γ)).indicator ht
  have hlocal (x : H) : ∑' γ : Γ, k (γ.val * x) ≤ A.indicator f (mk Γ x) := by
    by_cases hx : ∃ γ : Γ, γ.val * x ∈ t
    · obtain ⟨γ, hγ⟩ := hx
      have hkγ (δ : Γ) (hδ : δ ≠ γ) : k (δ.val * x) = 0 := by
        apply indicator_of_notMem
        intro hm
        have he := hinj hm hγ ((mk_subgroup_mul Γ δ x).trans (mk_subgroup_mul Γ γ x).symm)
        exact hδ (Subtype.ext (mul_right_cancel he))
      rw [tsum_eq_single γ hkγ]
      have hq : mk Γ x ∈ A := (mk_subgroup_mul Γ γ x) ▸ hmap hγ
      rw [indicator_of_mem hq]
      exact le_of_eq ((indicator_of_mem hγ _).trans (congrArg f (mk_subgroup_mul Γ γ x)))
    · have hz (γ : Γ) : k (γ.val * x) = 0 :=
        indicator_of_notMem (fun h => hx ⟨γ, h⟩) _
      simp only [hz, tsum_zero, zero_le]
  calc
    _ = ∫⁻ x, k x ∂ν := (lintegral_indicator ht _).symm
    _ = ∑' γ : Γ, ∫⁻ x in s, k (γ.val * x) ∂ν :=
      (isFundamentalDomain Γ hΓ ν).lintegral_eq_tsum'' k
    _ = ∫⁻ x in s, ∑' γ : Γ, k (γ.val * x) ∂ν := by
      rw [lintegral_tsum]
      intro γ
      exact (hk.comp (measurable_const.mul measurable_id)).aemeasurable
    _ ≤ ∫⁻ x in s, A.indicator f (mk Γ x) ∂ν := lintegral_mono hlocal
    _ = ∫⁻ q, A.indicator f q ∂discreteQuotientMeasure Γ hΓ ν :=
      (lintegral_map (hf.indicator hA) (measurable_mk Γ)).symm
    _ = _ := lintegral_indicator hA _

end Langlands.Global.LeftCosetSpace
