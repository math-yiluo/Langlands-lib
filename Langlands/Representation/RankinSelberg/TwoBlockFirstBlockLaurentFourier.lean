import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentMatrices
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-!
# The partial Fourier value on the first-block fiber

At `diag(v, 1) g` the plus-sign first-block partial Fourier value of `gΦ` is
`|det v|⁻¹ ∫ ψ((x v⁻¹)_0) Φ((x, η) g) dx`, for the supplied self-dual product measure.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open MeasureTheory GeneralLinear TwoBlockFirstBlockQuotient HarmonicAnalysis
  HarmonicAnalysis.TwoBlockRowPartialFourier TwoBlockLowerUnfolding

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- `(diag(v, 1) g Φ)~[ζ, η] = |det v|⁻¹ ∫ ψ((x v⁻¹)_0) Φ((x, η) g) dx`. -/
theorem partialSection_firstBlockEmbedding_mul :
    letI := F.canonicalTopologicalData.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
      (Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier))
      (v : GeneralLinear (m 0 + 1) F.Carrier) (g : GeneralLinear (t + 1) F.Carrier),
      partialSection h ψ μ Φ (firstBlockEmbedding h F.Carrier v * g) =
        ((F.canonicalTopologicalData.normalizedAbs (Matrix.det v.val))⁻¹ : ℂ) *
          ∫ x, ψ.complex (Matrix.vecMul x (v⁻¹).val 0) *
            Φ (Matrix.vecMul (join (succBlockEquiv h) x (eta (m 1))) g.val)
            ∂rowMeasure μ (m 0 + 1) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ μ Φ v g
  have := sigmaFinite_additiveHaarMeasure μ
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      μ.measure.map (fun x => a * x) = (T.normalizedAbsHom a)⁻¹ • μ.measure :=
    padicScalarHaarScaling F T μ.measure (Units.mk0 a ha)
  let H : (Fin (m 0 + 1) → F.Carrier) → ℂ := fun x =>
    ψ.complex (Matrix.vecMul x (v⁻¹).val 0) *
      Φ (Matrix.vecMul (join (succBlockEquiv h) x (eta (m 1))) g.val)
  have hL : MeasurableEmbedding (fun x : Fin (m 0 + 1) → F.Carrier => Matrix.vecMul x v.val) :=
    (rowHomeomorph v).measurableEmbedding
  rw [partialSection_apply]
  calc (∫ w, ψ.complex (w 0) *
        Φ (Matrix.vecMul (join (succBlockEquiv h) w (eta (m 1)))
          (firstBlockEmbedding h F.Carrier v * g).val) ∂rowMeasure μ (m 0 + 1))
      = ∫ w, H (Matrix.vecMul w v.val) ∂rowMeasure μ (m 0 + 1) := by
        congr 1
        funext w
        simp only [H]
        rw [Units.val_mul, ← Matrix.vecMul_vecMul, vecMul_join_eta_firstBlockEmbedding,
          Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.vecMul_one]
    _ = ∫ z, H z ∂((rowMeasure μ (m 0 + 1)).map fun x => Matrix.vecMul x v.val) :=
        (hL.integral_map H).symm
    _ = ∫ z, H z ∂((T.normalizedAbsHom (Matrix.det v.val))⁻¹ • rowMeasure μ (m 0 + 1)) := by
        rw [rowMeasure_map_vecMul T.normalizedAbsHom μ hχ v]
    _ = _ := by
        rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, NNReal.coe_inv,
          Complex.ofReal_inv]
        rfl

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
