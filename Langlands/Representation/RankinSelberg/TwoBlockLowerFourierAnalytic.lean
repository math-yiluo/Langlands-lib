import Langlands.Representation.RankinSelberg.TwoBlockLowerFourierMeasure
import Langlands.Representation.RankinSelberg.TwoBlockLowerFourierTransportStatement

/-! # Fourier specialization and coefficient change of variables -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFourier

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  TwoBlockLowerUnipotentQuotient TwoBlockLowerUnfolding
  HarmonicAnalysis.TwoBlockRowPartialFourier

universe uF uX uY

section Rows

variable {K : Type*} [Zero K] [One K]

theorem zeta_comp_rev (n : ℕ) : zeta (K := K) n ∘ Fin.rev = eta n := by
  funext i
  simp [zeta, eta, Fin.rev_eq_iff]

theorem eta_comp_rev (n : ℕ) : eta (K := K) n ∘ Fin.rev = zeta n := by
  funext i
  simp [zeta, eta, Fin.rev_eq_iff]

end Rows

section DualTest

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

theorem lowerDualTest_rotation {t : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i + 1) = t + 1) (ψ : UnitaryAdditiveCharacter K)
    (Wtest : WhittakerFunctions ψ t) (g : GeneralLinear (t + 1) K) :
    (firstDualFunction ψ t Wtest).val
        (blockRotation (reverse_sum h) K *
          (weylLong (t + 1) K * inverseTranspose (t + 1) K g)) =
      Wtest.val (blockRotation h K * g) := by
  rw [firstDualFunction_apply, dual_rotation]

end DualTest

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The published pure row identity, expressed at any equal contiguous total rank. -/
theorem rowCompanion_contiguous :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI : TotallyDisconnectedSpace F.Carrier := by
      let : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (μ : AdditiveHaarMeasure F.Carrier), IsSelfDual ψ μ →
      ∀ (a b N : ℕ) (hab : a + b = N) (hba : b + a = N),
        0 < a → 0 < b →
        ∀ (Φ Φhat : SchwartzBruhat (Fin N → F.Carrier)),
          IsRowFourierPair ψ μ Φ Φhat →
          ∀ (g : GeneralLinear N F.Carrier)
            (ξ : Fin b → F.Carrier) (η : Fin a → F.Carrier),
            (∫ u, ψ.complex (-rowPairing u ξ) *
                Φhat (Matrix.vecMul (join (contiguousEquiv hba) u η)
                  (weylLong N F.Carrier * inverseTranspose N F.Carrier g).val)
                ∂rowMeasure μ b) =
              (T.normalizedAbs (determinant g : F.Carrier) : ℂ) *
                ∫ w, ψ.complex (rowPairing w (η ∘ Fin.rev)) *
                  Φ (Matrix.vecMul (join (contiguousEquiv hab) w (ξ ∘ Fin.rev)) g.val)
                  ∂rowMeasure μ a := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ μ hsd a b N hab hba ha hb Φ Φhat hpair g ξ η
  subst N
  have hc := (twoBlockRowFourierCompanion p F ψ μ hsd a b ha hb).2 Φ Φhat hpair g ξ η
  have hdet : (T.normalizedAbs (determinant g : F.Carrier) : ℂ) ≠ 0 := by
    exact_mod_cast (T.normalizedAbs_pos (determinant g).ne_zero).ne'
  have hc' := hc.2.2
  change (T.normalizedAbs (determinant g : F.Carrier) : ℂ)⁻¹ * _ = _ at hc'
  have heq := congrArg
    (fun z : ℂ => (T.normalizedAbs (determinant g : F.Carrier) : ℂ) * z) hc'
  have hj (u : Fin b → F.Carrier) :
      join (contiguousEquiv hba) u η = twoBlockSwappedRow u η := by
    rw [join_contiguousEquiv]
    rfl
  have hj' (w : Fin a → F.Carrier) :
      join (contiguousEquiv rfl) w (ξ ∘ Fin.rev) = Fin.append w (ξ ∘ Fin.rev) := by
    rw [join_contiguousEquiv]
    rfl
  simpa only [hj, hj', ← mul_assoc, mul_inv_cancel₀ hdet, one_mul] using heq

/-- Specialization at the actual source rows and the actual lower partial sections. -/
theorem partialSection_fourier {t : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i + 1) = t + 1) :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI : TotallyDisconnectedSpace F.Carrier := by
      let : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (μ : AdditiveHaarMeasure F.Carrier), IsSelfDual ψ μ →
      ∀ (Φ Φhat : SchwartzBruhat (Fin (t + 1) → F.Carrier)),
        IsRowFourierPair ψ μ Φ Φhat →
        ∀ g : GeneralLinear (t + 1) F.Carrier,
          partialSection (reverse_sum h) (ψ.scale (-1)) μ Φhat
              (weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier g) =
            (T.normalizedAbs (determinant g : F.Carrier) : ℂ) *
              partialSection h ψ μ Φ g := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ μ hsd Φ Φhat hpair g
  have hc := rowCompanion_contiguous F ψ μ hsd (m 0 + 1) (m 1 + 1) (t + 1)
    (TwoBlockJacquet.blockRanks_add h)
    ((Nat.add_comm _ _).trans (TwoBlockJacquet.blockRanks_add h))
    (Nat.succ_pos _) (Nat.succ_pos _) Φ Φhat hpair g (zeta (m 1)) (eta (m 0))
  have hscale (x : F.Carrier) : (ψ.scale (-1)).complex x = ψ.complex (-x) := by
    simp [UnitaryAdditiveCharacter.complex_apply, UnitaryAdditiveCharacter.scale_apply]
  simp only [partialSection, rowPartialFourierIntegral, rowTranslate_apply, succBlockEquiv,
    hscale]
  simp only [zeta_comp_rev, eta_comp_rev] at hc
  convert hc using 1
  apply integral_congr_ae
  filter_upwards [] with u
  congr 2


end Padic

section Transport

variable {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]

/-- A positive constant pointwise comparison under an exact change of variables
gives integrability equivalence and both total Bochner integral formulas. -/
theorem scalar_transport (D : X ≃ᵐ Y) {μ : Measure X} {ν : Measure Y}
    (hD : MeasurePreserving D μ ν) (E : X → ℂ) (ED : Y → ℂ)
    (c : ℝ) (hc : 0 < c) (hE : ∀ᵐ x ∂μ, ED (D x) = (c : ℂ) * E x) :
    (Integrable ED ν ↔ Integrable E μ) ∧
      (∫ y, ED y ∂ν) = (c : ℂ) * ∫ x, E x ∂μ ∧
      (∫ y, ‖ED y‖ ∂ν) = c * ∫ x, ‖E x‖ ∂μ := by
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [← hD.integrable_comp_emb D.measurableEmbedding]
    exact (integrable_congr hE).trans
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc0) E)
  · rw [← hD.integral_comp' ED]
    exact (integral_congr_ae hE).trans (integral_const_mul _ _)
  · rw [← hD.integral_comp' (fun y => ‖ED y‖)]
    have hn : ∀ᵐ x ∂μ, ‖ED (D x)‖ = c * ‖E x‖ := hE.mono fun x hx => by
      rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    exact (integral_congr_ae hn).trans (integral_const_mul _ _)

end Transport

end Langlands.RankinSelberg.TwoBlockLowerFourier
