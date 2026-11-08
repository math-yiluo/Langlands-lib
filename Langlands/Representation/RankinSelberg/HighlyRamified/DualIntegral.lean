import Langlands.Representation.RankinSelberg.HighlyRamified.DualPointwise
import Langlands.Representation.RankinSelberg.LowerBlockQuotientDisintegrationProof
import Langlands.Representation.RankinSelberg.UnipotentQuotient
import Langlands.Representation.RankinSelberg.CanonicalCharacterChange
import Langlands.Representation.RankinSelberg.InducedTailIntermediateCanonicalMeasures

/-!
# Separating the last diagonal coordinate in a quotient integral

On `N_(m+2) \ GL_(m+2)` with the published lower-block disintegration
(`a = m + 1`, one final row), a measurable function whose chart values at `([A], x, c)`
are `κ(c)` times its values at `([A], x, 1)` integrates to `C (∫ κ dρ) ∫ f(chart(·,·,1))`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance dualIntegralFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance dualIntegralValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance dualIntegralLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance dualIntegralFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance dualIntegralFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance dualIntegralGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance dualIntegralGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance dualIntegralUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance dualIntegralUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance dualIntegralQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := borel _
local instance dualIntegralQuotientBorel (r : ℕ) : BorelSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := ⟨rfl⟩
local instance (priority := high) dualIntegralLowerMeasurable : MeasurableSpace
    (lowerTriangularSubgroup (0 + 1) F.Carrier) := borel _
local instance (priority := high) dualIntegralLowerBorel : BorelSpace
    (lowerTriangularSubgroup (0 + 1) F.Carrier) := ⟨rfl⟩

/-- The published disintegration of `unipotentQuotientHaar F (m+1)` along lower-block
coordinates with one final row, in an unconditional integral form: for every measurable
`f` with `f(chart(q,x,c)) = κ(c) f(chart(q,x,1))`, the integral separates. -/
theorem integral_separate_last (m : ℕ) (η : AdditiveHaarMeasure F.Carrier) :
    ∃ (ρ : Measure (lowerTriangularSubgroup (0 + 1) F.Carrier)) (C : ℝ), 0 < C ∧ SigmaFinite ρ ∧
      ∀ (f : LeftQuotient (upperUnipotent (m + 1 + 1) F.Carrier) → ℂ), Measurable f →
      ∀ κ : lowerTriangularSubgroup (0 + 1) F.Carrier → ℂ,
        (∀ q x c, f (lowerBlockQuotientChart (q, x, c)) =
          κ c * f (lowerBlockQuotientChart (q, x, 1))) →
        ∫ y, f y ∂unipotentQuotientHaar F.Carrier (m + 1) =
          (C : ℂ) * ((∫ c, κ c ∂ρ) * ∫ z, f (lowerBlockQuotientChart (z.1, z.2, 1))
            ∂((unipotentQuotientHaar F.Carrier m).withDensity
              (lowerBlockQuotientDensity F.canonicalTopologicalData (m + 1) 1)).prod
                (rectangularMeasure η 1 (m + 1))) := by
  obtain ⟨-, hmeas, -, -, ρ, -, hρσ, -, -, -, -, C, hC, -, hint⟩ :=
    lowerBlockQuotientDisintegration p F m 0 η (unipotentQuotientHaar F.Carrier m)
      (unipotentQuotientHaar F.Carrier (m + 1))
      (unipotentQuotientHaar_isCompatible F.Carrier m)
      (unipotentQuotientHaar_isCompatible F.Carrier (m + 1))
  refine ⟨ρ, C, hC, hρσ, fun f hf κ hsep => ?_⟩
  set μ' := (unipotentQuotientHaar F.Carrier m).withDensity
    (lowerBlockQuotientDensity F.canonicalTopologicalData (m + 1) 1) with hμ'
  set dx := rectangularMeasure η 1 (m + 1) with hdx
  have : SigmaFinite (unipotentQuotientHaar F.Carrier m) :=
    unipotentQuotientHaar_sigmaFinite_normalized F.canonicalTopologicalData m
  have step1 : ∫ y, f y ∂unipotentQuotientHaar F.Carrier (m + 1) =
      (C : ℂ) * ∫ z, f (lowerBlockQuotientChart z) ∂μ'.prod (dx.prod ρ) := by
    obtain ⟨hiff, heq⟩ := hint f hf
    by_cases hI : Integrable f (unipotentQuotientHaar F.Carrier (m + 1))
    · exact heq hI
    · have h2 : ¬ Integrable (fun z => f (lowerBlockQuotientChart z)) (μ'.prod (dx.prod ρ)) :=
        fun h => hI (hiff.mpr h)
      rw [integral_undef hI, integral_undef h2, mul_zero]
  have : SigmaFinite η.measure := InducedTailIntermediate.scalarHaar_sigmaFinite F.canonicalTopologicalData η
  have : SigmaFinite dx := by rw [hdx]; infer_instance
  have step2 : ∫ z, f (lowerBlockQuotientChart z) ∂μ'.prod (dx.prod ρ) =
      ∫ w, f (lowerBlockQuotientChart (MeasurableEquiv.prodAssoc w)) ∂(μ'.prod dx).prod ρ := by
    rw [← Measure.prodAssoc_prod (μ := μ') (ν := dx) (τ := ρ), integral_map_equiv]
  have step3 : ∫ w, f (lowerBlockQuotientChart (MeasurableEquiv.prodAssoc w)) ∂(μ'.prod dx).prod ρ
      = (∫ z, f (lowerBlockQuotientChart (z.1, z.2, 1)) ∂μ'.prod dx) * ∫ c, κ c ∂ρ := by
    rw [← integral_prod_mul]
    congr 1
    funext w
    change f (lowerBlockQuotientChart (w.1.1, w.1.2, w.2)) = _
    rw [hsep, mul_comm]
  rw [step1, step2, step3, mul_comm (∫ z, _ ∂μ'.prod dx)]

/-- Iterated form of `integral_separate_last`: for an integrable measurable `f` whose chart
values separate as `κ(c)` times their values at `c = 1`, with `0 < ∫⁻ ‖κ‖ dρ < ∞`, the integral
is `C (∫ κ dρ)` times the iterated integral `∫ |det|⁻¹ ∫ f(chart(q,x,1)) dx dμ_m`. -/
theorem integral_separate_last_iterated (m : ℕ) (η : AdditiveHaarMeasure F.Carrier) :
    ∃ (ρ : Measure (lowerTriangularSubgroup (0 + 1) F.Carrier)) (C : ℝ), 0 < C ∧ SigmaFinite ρ ∧
      (∀ K : OpenSubgroup (lowerTriangularSubgroup (0 + 1) F.Carrier),
        IsCompact (K : Set (lowerTriangularSubgroup (0 + 1) F.Carrier)) → 0 < ρ K ∧ ρ K < ⊤) ∧
      ∀ (f : LeftQuotient (upperUnipotent (m + 1 + 1) F.Carrier) → ℂ), Measurable f →
      ∀ κ : lowerTriangularSubgroup (0 + 1) F.Carrier → ℂ, Measurable κ →
        (∫⁻ c, ‖κ c‖ₑ ∂ρ) ≠ 0 → (∫⁻ c, ‖κ c‖ₑ ∂ρ) ≠ ⊤ →
        (∀ q x c, f (lowerBlockQuotientChart (q, x, c)) =
          κ c * f (lowerBlockQuotientChart (q, x, 1))) →
        Integrable f (unipotentQuotientHaar F.Carrier (m + 1)) →
        Integrable (fun q => ((lowerBlockQuotientDensity
              F.canonicalTopologicalData (m + 1) 1 q).toReal : ℂ) *
            ∫ x, f (lowerBlockQuotientChart (q, x, 1)) ∂rectangularMeasure η 1 (m + 1))
          (unipotentQuotientHaar F.Carrier m) ∧
        ∫ y, f y ∂unipotentQuotientHaar F.Carrier (m + 1) =
          (C : ℂ) * ((∫ c, κ c ∂ρ) * ∫ q, ((lowerBlockQuotientDensity
              F.canonicalTopologicalData (m + 1) 1 q).toReal : ℂ) *
            ∫ x, f (lowerBlockQuotientChart (q, x, 1)) ∂rectangularMeasure η 1 (m + 1)
              ∂unipotentQuotientHaar F.Carrier m) := by
  obtain ⟨-, hchart, -, -, ρ, -, hρσ, -, -, -, hρK, C, hC, -, hint⟩ :=
    lowerBlockQuotientDisintegration p F m 0 η (unipotentQuotientHaar F.Carrier m)
      (unipotentQuotientHaar F.Carrier (m + 1))
      (unipotentQuotientHaar_isCompatible F.Carrier m)
      (unipotentQuotientHaar_isCompatible F.Carrier (m + 1))
  refine ⟨ρ, C, hC, hρσ, hρK, fun f hf κ hκ hκ0 hκtop hsep hfi => ?_⟩
  set D := lowerBlockQuotientDensity F.canonicalTopologicalData (m + 1) 1 with hD
  set μ' := (unipotentQuotientHaar F.Carrier m).withDensity D with hμ'
  set dx := rectangularMeasure η 1 (m + 1) with hdx
  have : SigmaFinite (unipotentQuotientHaar F.Carrier m) :=
    unipotentQuotientHaar_sigmaFinite_normalized F.canonicalTopologicalData m
  have : SigmaFinite η.measure :=
    InducedTailIntermediate.scalarHaar_sigmaFinite F.canonicalTopologicalData η
  have : SigmaFinite dx := by rw [hdx]; infer_instance
  have hDmeas : Measurable D := measurable_lowerBlockQuotientDensity _ _ _
  have : SigmaFinite μ' := by
    rw [hμ']
    exact SigmaFinite.withDensity_of_ne_top' fun q => lowerBlockQuotientDensity_ne_top _ _ _ q
  -- the separated function
  set g : LeftQuotient (upperUnipotent (m + 1) F.Carrier) ×
      Matrix (Fin 1) (Fin (m + 1)) F.Carrier → ℂ :=
    fun z => f (lowerBlockQuotientChart (z.1, z.2, 1)) with hg
  have hgmeas : Measurable g := by
    refine hf.comp (hchart.comp ?_)
    exact measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  have hfc : Integrable (fun z => f (lowerBlockQuotientChart z)) (μ'.prod (dx.prod ρ)) :=
    (hint f hf).1.mp hfi
  have hgi : Integrable g (μ'.prod dx) := by
    refine ⟨hgmeas.aestronglyMeasurable, ?_⟩
    have h1 : ∫⁻ w, ‖f (lowerBlockQuotientChart (MeasurableEquiv.prodAssoc w))‖ₑ
        ∂(μ'.prod dx).prod ρ = (∫⁻ z, ‖g z‖ₑ ∂μ'.prod dx) * ∫⁻ c, ‖κ c‖ₑ ∂ρ := by
      rw [← lintegral_prod_mul hgmeas.enorm.aemeasurable hκ.enorm.aemeasurable]
      congr 1
      funext w
      change ‖f (lowerBlockQuotientChart (w.1.1, w.1.2, w.2))‖ₑ = _
      rw [hsep, enorm_mul, mul_comm]
    have h2 : ∫⁻ w, ‖f (lowerBlockQuotientChart (MeasurableEquiv.prodAssoc w))‖ₑ
        ∂(μ'.prod dx).prod ρ = ∫⁻ z, ‖f (lowerBlockQuotientChart z)‖ₑ ∂μ'.prod (dx.prod ρ) := by
      rw [← Measure.prodAssoc_prod (μ := μ') (ν := dx) (τ := ρ),
        lintegral_map_equiv]
    have hfin : ∫⁻ z, ‖f (lowerBlockQuotientChart z)‖ₑ ∂μ'.prod (dx.prod ρ) < ⊤ :=
      hfc.2
    rw [← h2, h1] at hfin
    rcases ENNReal.mul_lt_top_iff.mp hfin with h | h | h
    · exact h.1
    · change ∫⁻ z, ‖g z‖ₑ ∂μ'.prod dx < ⊤
      rw [h]; exact ENNReal.zero_lt_top
    · exact absurd h hκ0
  have step1 : ∫ y, f y ∂unipotentQuotientHaar F.Carrier (m + 1) =
      (C : ℂ) * ∫ z, f (lowerBlockQuotientChart z) ∂μ'.prod (dx.prod ρ) :=
    (hint f hf).2 hfi
  have step2 : ∫ z, f (lowerBlockQuotientChart z) ∂μ'.prod (dx.prod ρ) =
      ∫ w, f (lowerBlockQuotientChart (MeasurableEquiv.prodAssoc w)) ∂(μ'.prod dx).prod ρ := by
    rw [← Measure.prodAssoc_prod (μ := μ') (ν := dx) (τ := ρ), integral_map_equiv]
  have step3 : ∫ w, f (lowerBlockQuotientChart (MeasurableEquiv.prodAssoc w)) ∂(μ'.prod dx).prod ρ
      = (∫ z, g z ∂μ'.prod dx) * ∫ c, κ c ∂ρ := by
    rw [← integral_prod_mul]
    congr 1
    funext w
    change f (lowerBlockQuotientChart (w.1.1, w.1.2, w.2)) = _
    rw [hsep, mul_comm]
  have step4 : ∫ z, g z ∂μ'.prod dx =
      ∫ q, ((D q).toReal : ℂ) * ∫ x, f (lowerBlockQuotientChart (q, x, 1)) ∂dx
        ∂unipotentQuotientHaar F.Carrier m := by
    rw [integral_prod g hgi, hμ', integral_withDensity_eq_integral_toReal_smul hDmeas
      (Filter.Eventually.of_forall fun q => (lowerBlockQuotientDensity_ne_top _ _ _ q).lt_top)]
    congr 1
  refine ⟨?_, ?_⟩
  · have hi := hgi.integral_prod_left
    rw [hμ', integrable_withDensity_iff_integrable_smul' hDmeas
      (Filter.Eventually.of_forall fun q => (lowerBlockQuotientDensity_ne_top _ _ _ q).lt_top)] at hi
    refine hi.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [hg, Complex.real_smul]
  · rw [step1, step2, step3, step4, mul_comm (∫ z, _ ∂unipotentQuotientHaar F.Carrier m)]

end Langlands.RankinSelberg.HighlyRamified
