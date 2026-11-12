import Langlands.Representation.GodementJacquet.LocalTateFunctionalEquation
import Langlands.Representation.GodementJacquet.LocalTateConductorPreliminaries

/-! # Scalar Tate theory with its principal-unit conductor: the proof -/

noncomputable section

namespace Langlands.GodementJacquet

namespace LocalTate

open MeasureTheory HarmonicAnalysis Topology ValuativeRel Conductor RankinSelberg Polynomial
open GeneralLinear.Iwasawa
open scoped ENNReal NNReal

universe uF

namespace Normalization

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : Normalization F)
variable [MeasurableSpace Fˣ] [BorelSpace Fˣ]

section Generator

variable [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]

include ν in
/-- The reciprocal of the Euler polynomial lies in the Laurent span of the
rational Mellin values: it comes from the indicator of `O` when `a = 0` and from
the indicator of the principal-unit level `1 + ϖ ^ a O` otherwise. -/
theorem inv_eulerPoly_mem_zetaSpan {η : Fˣ →* ℂˣ} (hηc : Continuous η) {a : ℕ}
    (hη : N.IsUnitConductor η a) :
    (algebraMap ℂ[X] RationalFunctions (N.eulerPoly η a))⁻¹ ∈
      zetaSpan (scalarMellinRationalValues N.q N.abv (localMultiplicativeHaar F)
        (fun x => (η x : ℂ)) 1) := by
  obtain ⟨Φ, κ, hκ, h⟩ : ∃ Φ : SchwartzBruhat F, ∃ κ : ℂ, κ ≠ 0 ∧
      N.HasLaurentMellin η (N.eulerPoly η a) Φ (LaurentPolynomial.C κ) := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · refine ⟨N.cosetIndicator 0 0, 1, one_ne_zero, ?_⟩
      have h := N.hasLaurentMellin_integer hηc hη
      rwa [ite_eq_left ha] at h
    · refine ⟨N.cosetIndicator 1 a,
        ((localMultiplicativeHaar F (N.unitLevel a : Set Fˣ)).toReal : ℂ), ?_, ?_⟩
      · rw [N.measure_unitLevel ν ha]
        have hpos : 0 < (ν (N.ball a)).toReal / (ν (unitShell F)).toReal :=
          div_pos (ENNReal.toReal_pos (N.measure_ball_pos ν a).ne' (N.measure_ball_lt_top ν a).ne)
            (N.measure_unitShell_toReal_pos ν)
        exact_mod_cast hpos.ne'
      · refine (N.hasLaurentMellin_unitLevel hηc hη ha).congr N fun x => ?_
        simp [eulerPoly, ha.ne']
  have hR := N.hasRationalContinuation_of_hasLaurentMellin h
  have hmem := Submodule.smul_mem _ (LaurentPolynomial.C κ⁻¹)
    (mem_zetaSpan (values := scalarMellinRationalValues N.q N.abv (localMultiplicativeHaar F)
      (fun x => (η x : ℂ)) 1) ⟨Φ, hR⟩)
  convert hmem using 1
  rw [Algebra.smul_def, algebraMap_laurent, div_eq_mul_inv, ← mul_assoc, ← map_mul,
    ← map_mul, inv_mul_cancel₀ hκ, map_one, map_one, one_mul]

include ν in
/-- The Euler polynomial is the normalized generator of the rational Mellin values. -/
theorem isNormalizedGenerator_eulerPoly {η : Fˣ →* ℂˣ} (hηc : Continuous η) {a : ℕ}
    (hη : N.IsUnitConductor η a) :
    IsNormalizedGenerator
      (scalarMellinRationalValues N.q N.abv (localMultiplicativeHaar F) (fun x => (η x : ℂ)) 1)
      (N.eulerPoly η a) := by
  rw [isNormalizedGenerator_iff]
  refine ⟨N.eulerPoly_coeff_zero η a, ?_, N.inv_eulerPoly_mem_zetaSpan ν hηc hη⟩
  rintro f ⟨Φ, hf⟩
  obtain ⟨ℓ, hℓ⟩ := N.exists_hasLaurentMellin hηc hη Φ
  exact ⟨ℓ, N.laurentToRatFunc_eq_of_hasLaurentMellin hℓ hf⟩

include ν in
/-- Convergence, rational continuation and a common denominator. -/
theorem scalarMellinAnalyticData_of_isUnitConductor {η : Fˣ →* ℂˣ} (hηc : Continuous η)
    {a : ℕ} (hη : N.IsUnitConductor η a) :
    ScalarMellinAnalyticData N.q N.abv (localMultiplicativeHaar F) (fun x => (η x : ℂ)) 1 := by
  refine ⟨⟨Real.logb N.q ‖(η N.ϖ : ℂ)‖, fun Φ s hs => N.integrable_mellinIntegrand hηc Φ hs⟩,
    fun Φ => ?_, (N.isNormalizedGenerator_eulerPoly ν hηc hη).hasCommonDenominator⟩
  obtain ⟨ℓ, hℓ⟩ := N.exists_hasLaurentMellin hηc hη Φ
  exact ⟨_, N.hasRationalContinuation_of_hasLaurentMellin hℓ⟩

end Generator

section FunctionalEquation

variable [T2Space F] [TotallyDisconnectedSpace F] [MeasurableSpace F] [BorelSpace F]
  {ψ : UnitaryAdditiveCharacter F} (hψ : HasIntegerConductor ψ)
  {ν : AdditiveHaarMeasure F} (hν : IsSelfDual ψ ν)
  {χ : Fˣ →* ℂˣ} (hχc : Continuous χ) {a : ℕ} (hχ : N.IsUnitConductor χ a)
include hψ hν hχc hχ

/-- The Laurent functional equation holds for every Schwartz--Bruhat function. -/
theorem feData_all (Φ : SchwartzBruhat F) : N.FEData ψ ν χ a (N.feConstant ψ ν χ a) Φ := by
  refine N.schwartzBruhat_induction (p := N.FEData ψ ν χ a (N.feConstant ψ ν χ a))
    (N.feData_zero _) (fun f g hf hg => N.feData_add hf hg) (fun c f hf => N.feData_smul c hf)
    (fun x0 n => ?_) Φ
  by_cases hx0 : x0 ∈ N.ball n
  · rw [N.cosetIndicator_eq_dilate_of_mem hx0]
    exact N.feData_dilate _ (N.feData_integer hψ hχc hχ)
  · obtain ⟨m, hm, b, hb⟩ := N.cosetIndicator_eq_dilate_of_notMem hx0
    rw [hb]
    exact N.feData_dilate b (N.feData_unitLevel hψ hν hχc hχ hm)

/-- The constant of the functional equation is nonzero. For `a ≥ 1` this follows
by applying the Laurent functional equation to a Fourier preimage of the
indicator of `1 + ϖ ^ a O`, whose dual Mellin integral is a positive volume. -/
theorem feConstant_ne_zero : N.feConstant ψ ν χ a ≠ 0 := by
  intro h0
  rcases Nat.eq_zero_or_pos a with ha | ha
  · rw [feConstant, ite_eq_left ha] at h0
    have hpos := ENNReal.toReal_pos (N.measure_ball_pos ν.measure 0).ne'
      (N.measure_ball_lt_top ν.measure 0).ne
    exact hpos.ne' (by exact_mod_cast h0)
  · have hχc' : Continuous (χ⁻¹ : Fˣ →* ℂˣ) := continuous_inv.comp hχc
    obtain ⟨Φ0, hΦ0⟩ := exists_scalar_fourier_witness ψ ν hν (N.cosetIndicator (-1) a)
    obtain ⟨Ψ, hΨ, ℓ, ℓ', -, hℓ', hd⟩ := N.feData_all hψ hν hχc hχ Φ0
    have hfun : (Φ0 : F → ℂ) = fourierTransform ψ ν (N.cosetIndicator (-1) a) :=
      funext fun x => (hΦ0 x).2
    have hΨe : Ψ = N.cosetIndicator 1 a := by
      apply Subtype.ext
      funext y
      rw [hΨ y, hfun, (hν (N.cosetIndicator (-1) a)).2 y, cosetIndicator_apply,
        cosetIndicator_apply]
      apply indicator_one_congr
      have e : -y - -1 = -(y - 1) := by ring
      simp only [Set.mem_ofPred_eq]
      rw [e, neg_mem_iff]
    rw [hΨe] at hℓ'
    obtain ⟨σ1, h1⟩ := hℓ'
    obtain ⟨σ2, h2⟩ := N.hasLaurentMellin_unitLevel hχc' hχ.inv (m := a) ha
    set s : ℂ := ((max σ1 σ2 + 1 : ℝ) : ℂ)
    have hs1 : σ1 < s.re := by
      rw [Complex.ofReal_re]
      linarith [le_max_left σ1 σ2]
    have hs2 : σ2 < s.re := by
      rw [Complex.ofReal_re]
      linarith [le_max_right σ1 σ2]
    have e := (h1 s hs1).2.symm.trans (h2 s hs2).2
    have hz : laurentEval (spectralUnit N.q_pos s) ℓ' = 0 := by
      have h := hd (N.dualUnit (spectralUnit N.q_pos s))
      rwa [N.dualUnit_dualUnit, h0, zero_mul, zero_mul] at h
    rw [hz, map_mul, laurentEval_toLaurent, laurentEval_C, ite_eq_left le_rfl,
      N.measure_unitLevel ν.measure ha] at e
    simp only [eulerPoly, ha.ne', ↓reduceIte, eval_one, one_mul] at e
    have hpos : 0 < (ν.measure (N.ball a)).toReal / (ν.measure (unitShell F)).toReal :=
      div_pos (ENNReal.toReal_pos (N.measure_ball_pos ν.measure a).ne'
        (N.measure_ball_lt_top ν.measure a).ne) (N.measure_unitShell_toReal_pos ν.measure)
    exact hpos.ne' (by exact_mod_cast e.symm)

end FunctionalEquation

/-- The full conclusion for one normalization. -/
theorem localTateConductor_of_normalization [T2Space F] [TotallyDisconnectedSpace F]
    [MeasurableSpace F] [BorelSpace F] (χ : Fˣ →* ℂˣ) (hχc : Continuous χ)
    (ψ : UnitaryAdditiveCharacter F) (hψ : HasIntegerConductor ψ)
    (ν : AdditiveHaarMeasure F) (hν : IsSelfDual ψ ν) :
    ∃ a : ℕ,
      (∀ g ∈ levelSubgroup F 0 a, χ (GeneralLinear.determinant g) = 1) ∧
      (∀ b < a, ∃ g ∈ levelSubgroup F 0 b, χ (GeneralLinear.determinant g) ≠ 1) ∧
      ScalarMellinAnalyticData N.q N.abv (localMultiplicativeHaar F)
        (fun x => (χ x : ℂ)) 1 ∧
      ScalarMellinAnalyticData N.q N.abv (localMultiplicativeHaar F)
        (fun x => ((χ x)⁻¹ : ℂ)) 1 ∧
      let P : ℂ[X] := if a = 0 then 1 - C (χ N.ϖ : ℂ) * X else 1
      let PDual : ℂ[X] := if a = 0 then 1 - C ((χ N.ϖ)⁻¹ : ℂ) * X else 1
      IsNormalizedGenerator
        (scalarMellinRationalValues N.q N.abv (localMultiplicativeHaar F)
          (fun x => (χ x : ℂ)) 1) P ∧
      IsNormalizedGenerator
        (scalarMellinRationalValues N.q N.abv (localMultiplicativeHaar F)
          (fun x => ((χ x)⁻¹ : ℂ)) 1) PDual ∧
      ∃ c : ℂˣ, ∀ Φ : SchwartzBruhat F,
        ∃ Φhat : SchwartzBruhat F,
          (∀ y, Integrable (fun x => ψ.complex (x * y) * Φ x) ν.measure ∧
            Φhat y = fourierIntegral ψ ν Φ y) ∧
          ∀ R RDual : RationalFunctions,
            HasRationalContinuation N.q
              (scalarMellinIntegral N.abv (localMultiplicativeHaar F)
                (fun x => (χ x : ℂ)) 1 Φ) R →
            HasRationalContinuation N.q
              (scalarMellinIntegral N.abv (localMultiplicativeHaar F)
                (fun x => ((χ x)⁻¹ : ℂ)) 1 Φhat) RDual →
            NormalizedFunctionalEquation N.q P PDual 1 c 0 (a : ℤ) R RDual := by
  set a := characterConductor F χ hχc with ha_def
  have hspec := characterConductor_spec F χ hχc
  have hχ : N.IsUnitConductor χ a := (N.isUnitConductor_iff χ a).mpr hspec
  have hχc' : Continuous (χ⁻¹ : Fˣ →* ℂˣ) := continuous_inv.comp hχc
  have hfun : (fun x : Fˣ => ((χ x)⁻¹ : ℂ)) = fun x => ((χ⁻¹ x : ℂˣ) : ℂ) := by
    funext x
    simp
  refine ⟨a, hspec.1, hspec.2, N.scalarMellinAnalyticData_of_isUnitConductor ν.measure hχc hχ,
    ?_, ?_⟩
  · rw [hfun]
    exact N.scalarMellinAnalyticData_of_isUnitConductor ν.measure hχc' hχ.inv
  intro P PDual
  have hP : P = N.eulerPoly χ a := rfl
  have hPD : PDual = N.eulerPoly χ⁻¹ a := by
    simp [PDual, eulerPoly]
  rw [hP, hPD, hfun]
  refine ⟨N.isNormalizedGenerator_eulerPoly ν.measure hχc hχ,
    N.isNormalizedGenerator_eulerPoly ν.measure hχc' hχ.inv,
    Units.mk0 _ (N.feConstant_ne_zero hψ hν hχc hχ), fun Φ => ?_⟩
  obtain ⟨Ψ, hΨ, ℓ, ℓ', hℓ, hℓ', hd⟩ := N.feData_all hψ hν hχc hχ Φ
  refine ⟨Ψ, fun y => ⟨fourierIntegrand_integrable ψ ν Φ y, hΨ y⟩, fun R RDual hR hRD => ?_⟩
  have e1 := N.laurentToRatFunc_eq_of_hasLaurentMellin hℓ hR
  have e2 := N.laurentToRatFunc_eq_of_hasLaurentMellin hℓ' hRD
  intro s hs1 hs2
  have hx' : (N.dualUnit (spectralUnit N.q_pos s) : ℂ) = spectralPoint N.q (1 - s) :=
    N.coe_dualUnit_spectralUnit s
  have l1 := laurentEval_eq_of_laurentToRatFunc_eq (spectralUnit N.q_pos s) e1
    (by rwa [coe_spectralUnit])
  have l2 := laurentEval_eq_of_laurentToRatFunc_eq (N.dualUnit (spectralUnit N.q_pos s)) e2
    (by rwa [hx'])
  have h := hd (spectralUnit N.q_pos s)
  rw [l1, l2, hx', coe_spectralUnit] at h
  rw [h, epsilonMonomial, Units.val_one, one_pow, one_mul, Units.val_mk0]

end Normalization

end LocalTate

open LocalTate

/-- Scalar Tate theory over an arbitrary nonarchimedean local field with the
exact principal-unit conductor. -/
theorem localTateConductor : LocalTateConductorStatement.{uF} := by
  intro F _ _ _ _ _ _ _ _ _ _ q hq abv ϖ hϖ habvϖ habv1 χ hχc ψ hψ ν hν
  exact LocalTate.Normalization.localTateConductor_of_normalization
    ⟨q, hq, abv, ϖ, hϖ, habvϖ, habv1⟩ χ hχc ψ hψ ν hν

end Langlands.GodementJacquet
