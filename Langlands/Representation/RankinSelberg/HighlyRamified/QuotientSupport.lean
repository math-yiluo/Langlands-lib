import Langlands.Analysis.Local.QuotientMeasure
import Langlands.Representation.RankinSelberg.HighlyRamified.DualAverage

/-!
# Quotient integrals of functions supported on `H K`

For a compatible quotient measure on `H \ G` and a compact open subgroup `K` with
`μ_H(H ∩ K) = 1`, the quotient integral of a continuous left `H`-invariant function
supported on `H K` is the ambient Haar integral of its restriction to `K`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory QuotientIntegration

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) [MeasurableSpace H] [BorelSpace H] [MeasurableMul H]
variable (μG : Measure G) (μH : Measure H) [Measure.IsMulRightInvariant μH]
variable [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]

omit [BorelSpace G] [BorelSpace (LeftQuotient H)] in
/-- The quotient integral of a continuous left invariant function supported on `H K`. -/
theorem integral_out_of_support (ν : Measure (LeftQuotient H))
    (hν : IsCompatible H μG μH ν) (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    (hHK : μH {h : H | h.val ∈ K} = 1)
    (φ : G → ℂ) (hφ : Continuous φ) (hφH : ∀ (h : H) g, φ (h.val * g) = φ g)
    (hsupp : ∀ g, φ g ≠ 0 → ∃ h : H, h.val * g ∈ K) :
    ∫ q, φ q.out ∂ν = ∫ g, (K : Set G).indicator φ g ∂μG := by
  set f : G → ℂ := (K : Set G).indicator φ with hf
  have hfc : Continuous f := by
    classical
    rw [hf, ← Set.piecewise_eq_indicator]
    refine hφ.piecewise ?_ continuous_const
    rw [K.isClopen.frontier_eq]
    simp
  have hfs : HasCompactSupport f := by
    refine HasCompactSupport.intro hKc fun g hg => ?_
    simp [hf, Set.indicator_of_notMem hg]
  have hHKm : MeasurableSet {h : H | h.val ∈ K} :=
    (K.isOpen.preimage continuous_subtype_val).measurableSet
  have hpt : ∀ q : LeftQuotient H, quotientAverage H μH f q = φ q.out := by
    intro q
    conv_lhs => rw [← Quotient.out_eq q]
    rw [quotientAverage_mk]
    by_cases h0 : φ q.out = 0
    · rw [h0]
      have : ∀ h : H, f (h.val * q.out) = 0 := by
        intro h
        simp [hf, hφH, h0]
      simp [this]
    · obtain ⟨h₀, hh₀⟩ := hsupp _ h0
      have hval : ∀ h : H, f (h.val * q.out) =
          ({h : H | h.val ∈ K}.indicator (fun _ => (1 : ℂ)) (h * h₀⁻¹)) * φ q.out := by
        intro h
        have hiff : h.val * q.out ∈ K ↔ (h * h₀⁻¹).val ∈ K := by
          have e : h.val * q.out = (h * h₀⁻¹).val * (h₀.val * q.out) := by
            simp [mul_assoc]
          rw [e]
          constructor
          · intro hm
            have := K.mul_mem hm (K.inv_mem hh₀)
            simpa [mul_assoc] using this
          · intro hm
            exact K.mul_mem hm hh₀
        by_cases hm : h.val * q.out ∈ K
        · rw [hf, Set.indicator_of_mem hm, hφH,
            Set.indicator_of_mem (show h * h₀⁻¹ ∈ {h : H | h.val ∈ K} from hiff.mp hm)]
          ring
        · rw [hf, Set.indicator_of_notMem hm,
            Set.indicator_of_notMem (show h * h₀⁻¹ ∉ {h : H | h.val ∈ K} from
              fun h' => hm (hiff.mpr h'))]
          ring
      simp_rw [hval]
      rw [integral_mul_const]
      have hshift := integral_mul_right_eq_self (μ := μH)
        (fun h : H => {h : H | h.val ∈ K}.indicator (fun _ => (1 : ℂ)) h) h₀⁻¹
      rw [hshift, integral_indicator_const _ hHKm, measureReal_def, hHK]
      simp
  rw [← hν.integral_formula f hfc hfs]
  exact integral_congr_ae (Filter.Eventually.of_forall fun q => (hpt q).symm)

end Langlands.RankinSelberg.HighlyRamified
