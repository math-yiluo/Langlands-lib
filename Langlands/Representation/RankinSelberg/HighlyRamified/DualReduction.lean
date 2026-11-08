import Langlands.Representation.RankinSelberg.HighlyRamified.DualIntegral
import Langlands.Representation.RankinSelberg.HighlyRamified.DualSmear
import Langlands.Group.GL.IntegralSubgroup

/-!
# Reduction of the dual corank-one integral to one rank lower

For the candidate test function and a dual test function that is right equivariant under
`diag(I, c)`, `c ∈ O^×`, the dual corank-one integral over `N_(m+2) \ GL_(m+2)` equals a
positive constant times an integral over `N_(m+1) \ GL_(m+1)` of
`|det A|⁻¹ χ(det w) χ(det A)⁻¹ |det A|^(s-1/2) W(M(diag(A,1))) Ψ(A)`, where
`Ψ(A) = ∫ S2(rev x) f̃([[A,0],[x,1]]) dx`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance dualReductionFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance dualReductionValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance dualReductionLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance dualReductionFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance dualReductionFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance dualReductionGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance dualReductionGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance dualReductionUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance dualReductionUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance dualReductionQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := borel _
local instance dualReductionQuotientBorel (r : ℕ) : BorelSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := ⟨rfl⟩
local instance (priority := high) dualReductionLowerMeasurable : MeasurableSpace
    (lowerTriangularSubgroup (0 + 1) F.Carrier) := borel _
local instance (priority := high) dualReductionLowerBorel : BorelSpace
    (lowerTriangularSubgroup (0 + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The normalized absolute value is `1` on integral units. -/
theorem abv_eq_one_of_unit {c : F.Carrier} (hc : c ∈ (ValuativeRel.valuation F.Carrier).integer) (hne : c ≠ 0) (hinv : c⁻¹ ∈ (ValuativeRel.valuation F.Carrier).integer) :
    abv c = 1 := by
  have h1 : abv c ≤ 1 :=
    (F.canonicalTopologicalData.normalizedAbs_le_one_iff_mem_integers c).mpr hc
  have h2 : abv c⁻¹ ≤ 1 :=
    (F.canonicalTopologicalData.normalizedAbs_le_one_iff_mem_integers c⁻¹).mpr hinv
  have hprod : abv c * abv c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hne, map_one]
  have hpos : 0 ≤ abv c := (abv).nonneg c
  have hpos' : 0 ≤ abv c⁻¹ := (abv).nonneg c⁻¹
  nlinarith

/-- The open subgroup of integral units in the lower triangular group of `GL_1`. -/
def unitLowerSubgroup : OpenSubgroup (lowerTriangularSubgroup (0 + 1) F.Carrier) where
  toSubgroup := (Langlands.GeneralLinearGroup.integralSubgroup (Fin (0 + 1)) (ValuativeRel.valuation F.Carrier).integer).comap
    (lowerTriangularSubgroup (0 + 1) F.Carrier).subtype
  isOpen' := (Langlands.GeneralLinearGroup.isOpen_integralSubgroup (Fin (0 + 1)) (ValuativeRel.valuation F.Carrier).integer
    (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier))).preimage
      continuous_subtype_val

theorem mem_unitLowerSubgroup (c : lowerTriangularSubgroup (0 + 1) F.Carrier) :
    c ∈ unitLowerSubgroup F ↔ c.val 0 0 ∈ (ValuativeRel.valuation F.Carrier).integer ∧ (c.val⁻¹ : GeneralLinear (0 + 1) F.Carrier) 0 0 ∈ (ValuativeRel.valuation F.Carrier).integer := by
  change c.val ∈ Langlands.GeneralLinearGroup.integralSubgroup (Fin (0 + 1)) (ValuativeRel.valuation F.Carrier).integer ↔ _
  rw [Langlands.GeneralLinearGroup.mem_integralSubgroup]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1 0 0, h2 0 0⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; exact h1,
      fun i j => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; exact h2⟩

theorem isCompact_unitLowerSubgroup :
    IsCompact ((unitLowerSubgroup F : Subgroup (lowerTriangularSubgroup (0 + 1) F.Carrier)) :
      Set (lowerTriangularSubgroup (0 + 1) F.Carrier)) := by
  have := localField_t2 F.Carrier
  have hO : IsCompact ((ValuativeRel.valuation F.Carrier).integer : Set F.Carrier) :=
    isCompact_iff_compactSpace.mpr
      (inferInstanceAs (CompactSpace (ValuativeRel.valuation F.Carrier).integer))
  have hK := Langlands.GeneralLinearGroup.isCompact_integralSubgroup (Fin (0 + 1)) (ValuativeRel.valuation F.Carrier).integer hO
  exact (lowerTriangularSubgroup_isClosed (R := F.Carrier) (0 + 1)).isClosedEmbedding_subtypeVal
    |>.isCompact_preimage hK

section Reduction

variable {m : ℕ}

/-- The dual corank-one integrand of the candidate test function at a chart point. -/
theorem dualIntegrand_chart (ψ : UnitaryAdditiveCharacter F.Carrier) (χ : F.Carrierˣ →* ℂˣ)
    (W : WhittakerFunctions ψ (m + 2)) (T : Finset (Fin (m + 2) → F.Carrier))
    (Φ : (Fin (m + 2) → F.Carrier) → ℂ) (Fc : WhittakerFunctions ψ (m + 2))
    (hFc : Fc.val = candidateTest ψ χ W T Φ)
    (f' : InverseWhittakerFunctions ψ (m + 1)) (s : ℂ)
    (A : GeneralLinear (m + 1) F.Carrier) (x : Matrix (Fin 1) (Fin (m + 1)) F.Carrier)
    (c : lowerTriangularSubgroup (0 + 1) F.Carrier) :
    corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) Fc)
        (secondDualFunction ψ (m + 1) f') s
        (lowerBlockQuotientChart (Quotient.mk _ A, x, c)) =
      candidateTest ψ χ W T Φ (weylLong (m + 3) F.Carrier * inverseTranspose (m + 3) F.Carrier
          (rankInclusion 1 (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F.Carrier))) *
        (secondDualFunction ψ (m + 1) f').val
          (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F.Carrier) *
        determinantWeight abv (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F.Carrier)
          (s - 1 / 2) := by
  rw [lowerBlockQuotientChart_mk, corankOneIntegrand_mk, firstDualFunction_apply, hFc]

/-- The weight in the last diagonal coordinate. -/
def lastWeight (χ : F.Carrierˣ →* ℂˣ) (S1 η : F.Carrier → ℂ)
    (c : lowerTriangularSubgroup (0 + 1) F.Carrier) : ℂ :=
  S1 (c.val 0 0) * ((χ (determinant c.val) : ℂ))⁻¹ * η (c.val 0 0)

/-- The dual integrand at a chart point, in separated form. -/
theorem dualIntegrand_chart_separated {f : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
    (χ : F.Carrierˣ →* ℂˣ)
    (W : WhittakerFunctions ψ (m + 2)) (T : Finset (Fin (m + 2) → F.Carrier))
    (Φ : (Fin (m + 2) → F.Carrier) → ℂ) (Fc : WhittakerFunctions ψ (m + 2))
    (hFc : Fc.val = candidateTest ψ χ W T Φ)
    (S1 : F.Carrier → ℂ) (S2 : (Fin (m + 1) → F.Carrier) → ℂ) (η : F.Carrier → ℂ)
    (f' : InverseWhittakerFunctions ψ (m + 1))
    (hψ : ∀ t : F.Carrier, t ∉ (ValuativeRel.valuation F.Carrier).integer →
      ∃ z ∈ (ValuativeRel.valuation F.Carrier).integer, ψ.complex (z * t) ≠ 1)
    (hfac : ∀ ξ : Fin (m + 2) → F.Carrier,
      (∀ k, ξ k ∈ (ValuativeRel.valuation F.Carrier).integer) →
      finiteFourier ψ T Φ ξ = S1 (ξ 0) * S2 (fun k => ξ k.succ))
    (hS1 : ∀ c, S1 c ≠ 0 → c ∈ (ValuativeRel.valuation F.Carrier).integer ∧ c ≠ 0 ∧
      c⁻¹ ∈ (ValuativeRel.valuation F.Carrier).integer)
    (hS2 : ∀ v, S2 v ≠ 0 → ∀ k, ∃ y : (ValuativeRel.valuation F.Carrier).integer,
      y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F.Carrier).integer ^ f ∧
        (y : F.Carrier) = v k)
    (hK : ∀ g k, k ∈ Conductor.levelSubgroup F.Carrier (m + 2) f → W.val (g * k) = W.val g)
    (hη : ∀ (y : GeneralLinear (m + 1 + 1) F.Carrier) (c : lowerTriangularSubgroup 1 F.Carrier),
      c.val 0 0 ∈ (ValuativeRel.valuation F.Carrier).integer →
      (c.val 0 0)⁻¹ ∈ (ValuativeRel.valuation F.Carrier).integer →
        (secondDualFunction ψ (m + 1) f').val
            (y * (lowerBlockPair 1 0 c : GeneralLinear (m + 1 + 1) F.Carrier)) =
          η (c.val 0 0) * (secondDualFunction ψ (m + 1) f').val y)
    (s : ℂ) (A : GeneralLinear (m + 1) F.Carrier) (x : Matrix (Fin 1) (Fin (m + 1)) F.Carrier)
    (c : lowerTriangularSubgroup (0 + 1) F.Carrier) :
    corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) Fc)
        (secondDualFunction ψ (m + 1) f') s
        (lowerBlockQuotientChart (Quotient.mk _ A, x, c)) =
      (χ (determinant (weylLong (m + 3) F.Carrier)) : ℂ) * lastWeight F χ S1 η c *
        (S2 (fun k => x 0 k.rev) * ((χ (determinant A) : ℂ))⁻¹ *
          (secondDualFunction ψ (m + 1) f').val
            (lowerBlockPair A x 1 : GeneralLinear (m + 1 + 1) F.Carrier) *
          determinantWeight abv A (s - 1 / 2) *
          W.val (dualConj (rankInclusion 1 A))) := by
  rw [dualIntegrand_chart F ψ χ W T Φ Fc hFc f' s A x c]
  exact candidateTest_dual_lowerBlockPair ψ χ W T Φ S1 S2 η _ abv hψ hfac hS1 hS2 hK hη
    (fun c hc hne hinv => abv_eq_one_of_unit F hc hne hinv) A x c s

/-- The dual corank-one integral of the candidate test function, reduced to one rank lower.
There is a positive constant `C'`, depending only on the rank and the Haar measure `ηH`, such
that, whenever the last-coordinate weight is the indicator of the integral units and the
integrand is measurable and integrable, the integral equals `C'` times the iterated integral
`∫ |det|⁻¹ ∫ f(chart(q,x,1)) dx`, and each inner integral at `[A]` is
`χ(det w) χ(det A)⁻¹ |det A|^(s-1/2) W(M(diag(A,1))) ∫ S2(rev x) f̃([[A,0],[x,1]]) dx`. -/
theorem dual_integral_reduction (ηH : AdditiveHaarMeasure F.Carrier) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ {f : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
      (χ : F.Carrierˣ →* ℂˣ)
      (W : WhittakerFunctions ψ (m + 2)) (T : Finset (Fin (m + 2) → F.Carrier))
      (Φ : (Fin (m + 2) → F.Carrier) → ℂ) (Fc : WhittakerFunctions ψ (m + 2))
      (_hFc : Fc.val = candidateTest ψ χ W T Φ)
      (S1 : F.Carrier → ℂ) (S2 : (Fin (m + 1) → F.Carrier) → ℂ) (η : F.Carrier → ℂ)
      (f' : InverseWhittakerFunctions ψ (m + 1))
      (_hψ : ∀ t : F.Carrier, t ∉ (ValuativeRel.valuation F.Carrier).integer →
        ∃ z ∈ (ValuativeRel.valuation F.Carrier).integer, ψ.complex (z * t) ≠ 1)
      (_hfac : ∀ ξ : Fin (m + 2) → F.Carrier,
        (∀ k, ξ k ∈ (ValuativeRel.valuation F.Carrier).integer) →
        finiteFourier ψ T Φ ξ = S1 (ξ 0) * S2 (fun k => ξ k.succ))
      (_hS1 : ∀ c, S1 c ≠ 0 → c ∈ (ValuativeRel.valuation F.Carrier).integer ∧ c ≠ 0 ∧
        c⁻¹ ∈ (ValuativeRel.valuation F.Carrier).integer)
      (_hS2 : ∀ v, S2 v ≠ 0 → ∀ k, ∃ y : (ValuativeRel.valuation F.Carrier).integer,
        y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F.Carrier).integer ^ f ∧
          (y : F.Carrier) = v k)
      (_hK : ∀ g k, k ∈ Conductor.levelSubgroup F.Carrier (m + 2) f → W.val (g * k) = W.val g)
      (_hη : ∀ (y : GeneralLinear (m + 1 + 1) F.Carrier)
        (c : lowerTriangularSubgroup 1 F.Carrier),
        c.val 0 0 ∈ (ValuativeRel.valuation F.Carrier).integer →
        (c.val 0 0)⁻¹ ∈ (ValuativeRel.valuation F.Carrier).integer →
          (secondDualFunction ψ (m + 1) f').val
              (y * (lowerBlockPair 1 0 c : GeneralLinear (m + 1 + 1) F.Carrier)) =
            η (c.val 0 0) * (secondDualFunction ψ (m + 1) f').val y)
      (_hκ : ∀ c, lastWeight F χ S1 η c =
        ((unitLowerSubgroup F : Set (lowerTriangularSubgroup (0 + 1) F.Carrier))).indicator 1 c)
      (s : ℂ),
      Measurable (corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) Fc)
        (secondDualFunction ψ (m + 1) f') s) →
      Integrable (corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) Fc)
        (secondDualFunction ψ (m + 1) f') s) (unipotentQuotientHaar F.Carrier (m + 1)) →
      Integrable (fun q => ((lowerBlockQuotientDensity F.canonicalTopologicalData (m + 1) 1 q).toReal : ℂ) *
          ∫ x, corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) Fc)
            (secondDualFunction ψ (m + 1) f') s (lowerBlockQuotientChart (q, x, 1))
            ∂rectangularMeasure ηH 1 (m + 1)) (unipotentQuotientHaar F.Carrier m) ∧
      corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier (m + 1))
          (firstDualFunction ψ (m + 2) Fc) (secondDualFunction ψ (m + 1) f') s =
        (C' : ℂ) * ∫ q, ((lowerBlockQuotientDensity F.canonicalTopologicalData (m + 1) 1 q).toReal : ℂ) *
          ∫ x, corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) Fc)
            (secondDualFunction ψ (m + 1) f') s (lowerBlockQuotientChart (q, x, 1))
            ∂rectangularMeasure ηH 1 (m + 1) ∂unipotentQuotientHaar F.Carrier m := by
  obtain ⟨ρ, C, hC, hρσ, hρK, hsep⟩ := integral_separate_last_iterated F m ηH
  set U : Set (lowerTriangularSubgroup (0 + 1) F.Carrier) :=
    ((unitLowerSubgroup F : Subgroup (lowerTriangularSubgroup (0 + 1) F.Carrier)) :
      Set (lowerTriangularSubgroup (0 + 1) F.Carrier)) with hU
  obtain ⟨hU0, hUtop⟩ := hρK (unitLowerSubgroup F) (isCompact_unitLowerSubgroup F)
  have hUm : MeasurableSet U := (unitLowerSubgroup F).isOpen.measurableSet
  refine ⟨C * (ρ U).toReal, mul_pos hC (ENNReal.toReal_pos hU0.ne' hUtop.ne), ?_⟩
  intro f ψ χ W T Φ Fc hFc S1 S2 η f' hψ hfac hS1 hS2 hK hη hκ s hmeas hint
  set κ : lowerTriangularSubgroup (0 + 1) F.Carrier → ℂ := U.indicator 1 with hκdef
  have hκeq : ∀ c, lastWeight F χ S1 η c = κ c := hκ
  have hκmeas : Measurable κ := measurable_const.indicator hUm
  have hlin : ∫⁻ c, ‖κ c‖ₑ ∂ρ = ρ U := by
    have : (fun c => ‖κ c‖ₑ) = U.indicator 1 := by
      funext c
      by_cases hc : c ∈ U <;> simp [hκdef, hc]
    rw [this, lintegral_indicator_one hUm]
  have hsepκ : ∀ q x c, corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) Fc)
      (secondDualFunction ψ (m + 1) f') s (lowerBlockQuotientChart (q, x, c)) =
      κ c * corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) Fc)
        (secondDualFunction ψ (m + 1) f') s (lowerBlockQuotientChart (q, x, 1)) := by
    intro q x c
    induction q using Quotient.inductionOn with
    | h A =>
      rw [dualIntegrand_chart_separated F ψ χ W T Φ Fc hFc S1 S2 η f' hψ hfac hS1 hS2 hK hη s A x c,
        dualIntegrand_chart_separated F ψ χ W T Φ Fc hFc S1 S2 η f' hψ hfac hS1 hS2 hK hη s A x 1,
        hκeq, hκeq]
      have h1 : κ 1 = 1 := by simp [hκdef, U, one_mem]
      rw [h1]
      ring
  obtain ⟨hmi, hmain⟩ := hsep _ hmeas κ hκmeas (by rw [hlin]; exact hU0.ne')
    (by rw [hlin]; exact hUtop.ne) hsepκ hint
  refine ⟨hmi, ?_⟩
  rw [corankOneIntegral, hmain]
  have hint1 : ∫ c, κ c ∂ρ = ((ρ U).toReal : ℂ) := by
    rw [hκdef, integral_indicator hUm]
    simp [Measure.real]
  rw [hint1]
  push_cast
  ring

/-- The inner integral at `[A]` of the reduced dual integral. -/
theorem dual_inner_integral {f : ℕ} (ηH : AdditiveHaarMeasure F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (χ : F.Carrierˣ →* ℂˣ)
    (W : WhittakerFunctions ψ (m + 2)) (T : Finset (Fin (m + 2) → F.Carrier))
    (Φ : (Fin (m + 2) → F.Carrier) → ℂ) (Fc : WhittakerFunctions ψ (m + 2))
    (hFc : Fc.val = candidateTest ψ χ W T Φ)
    (S1 : F.Carrier → ℂ) (S2 : (Fin (m + 1) → F.Carrier) → ℂ) (η : F.Carrier → ℂ)
    (f' : InverseWhittakerFunctions ψ (m + 1))
    (hψ : ∀ t : F.Carrier, t ∉ (ValuativeRel.valuation F.Carrier).integer →
      ∃ z ∈ (ValuativeRel.valuation F.Carrier).integer, ψ.complex (z * t) ≠ 1)
    (hfac : ∀ ξ : Fin (m + 2) → F.Carrier,
      (∀ k, ξ k ∈ (ValuativeRel.valuation F.Carrier).integer) →
      finiteFourier ψ T Φ ξ = S1 (ξ 0) * S2 (fun k => ξ k.succ))
    (hS1 : ∀ c, S1 c ≠ 0 → c ∈ (ValuativeRel.valuation F.Carrier).integer ∧ c ≠ 0 ∧
      c⁻¹ ∈ (ValuativeRel.valuation F.Carrier).integer)
    (hS2 : ∀ v, S2 v ≠ 0 → ∀ k, ∃ y : (ValuativeRel.valuation F.Carrier).integer,
      y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F.Carrier).integer ^ f ∧
        (y : F.Carrier) = v k)
    (hK : ∀ g k, k ∈ Conductor.levelSubgroup F.Carrier (m + 2) f → W.val (g * k) = W.val g)
    (hη : ∀ (y : GeneralLinear (m + 1 + 1) F.Carrier) (c : lowerTriangularSubgroup 1 F.Carrier),
      c.val 0 0 ∈ (ValuativeRel.valuation F.Carrier).integer →
      (c.val 0 0)⁻¹ ∈ (ValuativeRel.valuation F.Carrier).integer →
        (secondDualFunction ψ (m + 1) f').val
            (y * (lowerBlockPair 1 0 c : GeneralLinear (m + 1 + 1) F.Carrier)) =
          η (c.val 0 0) * (secondDualFunction ψ (m + 1) f').val y)
    (hκ1 : lastWeight F χ S1 η 1 = 1) (s : ℂ) (A : GeneralLinear (m + 1) F.Carrier) :
    ∫ x, corankOneIntegrand (ψ.scale (-1)) abv (firstDualFunction ψ (m + 2) Fc)
        (secondDualFunction ψ (m + 1) f') s
        (lowerBlockQuotientChart (Quotient.mk _ A, x, 1)) ∂rectangularMeasure ηH 1 (m + 1) =
      (χ (determinant (weylLong (m + 3) F.Carrier)) : ℂ) * ((χ (determinant A) : ℂ))⁻¹ *
        determinantWeight abv A (s - 1 / 2) * W.val (dualConj (rankInclusion 1 A)) *
        ∫ x, S2 (fun k => x 0 k.rev) * (secondDualFunction ψ (m + 1) f').val
          (lowerBlockPair A x 1 : GeneralLinear (m + 1 + 1) F.Carrier)
          ∂rectangularMeasure ηH 1 (m + 1) := by
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [dualIntegrand_chart_separated F ψ χ W T Φ Fc hFc S1 S2 η f' hψ hfac hS1 hS2 hK hη s A x 1,
    hκ1]
  ring

end Reduction

end Langlands.RankinSelberg.HighlyRamified
