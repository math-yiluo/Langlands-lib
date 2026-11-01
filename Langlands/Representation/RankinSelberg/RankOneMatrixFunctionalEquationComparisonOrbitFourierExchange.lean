import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierExchange
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonReflectedHaar
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFramedIntegrability
import Langlands.HarmonicAnalysis.RectangularFourierEquiv

/-! Actual inverse-character orbit Fourier exchange on unipotent times matrices. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.CompactWhittakerSynthesis

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis GeneralLinear Whittaker Topology

universe uK uF

section General

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

variable [MeasurableSpace K]

/-- The actual Fourier-side orbit kernel, in the unsigned long-Weyl convention. -/
def unipotentMatrixFourierDualKernel
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) K))
    (z : upperUnipotent (n + 1) K × Matrix (Fin (n + 1)) (Fin (n + 1)) K) : ℂ :=
  (inverseStandardCharacter ψ n z.1 : ℂ) *
    rectangularFourierIntegral ψ ν Φ
      ((inverseTranspose (n + 1) K z.1.val * weylLong (n + 1) K).val * z.2) * Ψ z.2

/-- The original-side kernel obtained from the same two tests by bilinear exchange. -/
def unipotentMatrixFourierOriginalKernel
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) K))
    (z : upperUnipotent (n + 1) K × Matrix (Fin (n + 1)) (Fin (n + 1)) K) : ℂ :=
  (inverseStandardCharacter ψ n z.1 : ℂ) * Φ z.2 *
    rectangularFourierIntegral ψ ν Ψ
      ((weylLong (n + 1) K * z.1.val⁻¹).val * z.2)

end General

section CanonicalPadic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

private theorem continuous_standardPhase (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ) :
    Continuous (fun u : upperUnipotent (n + 1) F.Carrier =>
      (standardCharacter ψ n u : ℂ)) :=
  Units.continuous_val.comp (standardCharacterContinuous ψ n).continuous

/-- Genuine joint convergence of the Fourier side follows from reflection and
the actual positive-level box frame; the transformed first test may meet singular matrices. -/
theorem integrable_unipotentMatrixFourierDualKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΨ : tsupport (Ψ : _ → ℂ) ⊆ RankOneBox.box F A q a) :
    Integrable (unipotentMatrixFourierDualKernel ψ ν n Φ Ψ)
      ((unipotentHaar F.Carrier n).prod (rectangularMeasure ν (n + 1) (n + 1))) := by
  let Φhat := rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ
  let Φhatw := rectangularLeftRightTranslate (weylLong (n + 1) F.Carrier) 1 Φhat
  have hi := integrable_weighted_framed_matrix_product (n + 1)
    (upperUnipotent (n + 1) F.Carrier) UpperUnipotent.isClosed
    (fun u => unipotent_det u) (firstColumnFrame n) (continuous_firstColumnFrame n)
    (firstColumnFrame_mul n) (unipotentHaar F.Carrier n)
    (rectangularMeasure ν (n + 1) (n + 1)) Φhatw Ψ
    (fun X hX => firstColumnFrame_mem_range_of_mem_box F n A q ha X (hΨ hX))
    (fun u => (standardCharacter ψ n u : ℂ)) (fun _ => 1)
    (continuous_standardPhase F ψ n) continuous_const
  have hp := measurePreserving_reflectedUnipotent_prod n
    (unipotentHaar F.Carrier n) (rectangularMeasure ν (n + 1) (n + 1))
  have h := hp.integrable_comp_of_integrable hi
  have hw (u : upperUnipotent (n + 1) F.Carrier) :
      weylLong (n + 1) F.Carrier * (reflectedUnipotent u).val =
        inverseTranspose (n + 1) F.Carrier u.val * weylLong (n + 1) F.Carrier := by
    simp only [reflectedUnipotent_val, ← mul_assoc, weylLong_mul_self, one_mul]
  unfold unipotentMatrixFourierDualKernel
  simpa only [Function.comp_def, Φhatw, rectangularLeftRightTranslate_apply,
    Units.val_one, Matrix.mul_one, standardCharacter_reflected, mul_one,
    ← Matrix.mul_assoc, ← Units.val_mul, hw, Φhat, rectangularFourierEquiv_apply] using h

/-- Genuine joint convergence of the original side, using only invertible
support of the fixed lift and the same supplied Haar measures. -/
theorem integrable_unipotentMatrixFourierOriginalKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    Integrable (unipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ)
      ((unipotentHaar F.Carrier n).prod (rectangularMeasure ν (n + 1) (n + 1))) := by
  let Ψhat := rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Ψ
  let Ψhatw := rectangularLeftRightTranslate (weylLong (n + 1) F.Carrier) 1 Ψhat
  have hi := integrable_weighted_framed_matrix_product (n + 1)
    (upperUnipotent (n + 1) F.Carrier) UpperUnipotent.isClosed
    (fun u => unipotent_det u) id continuous_id (fun _ _ => rfl)
    (unipotentHaar F.Carrier n) (rectangularMeasure ν (n + 1) (n + 1)) Ψhatw Φ
    (fun X hX => hΦ hX)
    (fun u => (standardCharacter ψ n u : ℂ)) (fun _ => 1)
    (continuous_standardPhase F ψ n) continuous_const
  have hp := (Measure.measurePreserving_inv (unipotentHaar F.Carrier n)).prod
    (MeasurePreserving.id (rectangularMeasure ν (n + 1) (n + 1)))
  have h := hp.integrable_comp_of_integrable hi
  unfold unipotentMatrixFourierOriginalKernel
  simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, Ψhatw,
    rectangularLeftRightTranslate_apply,
    Units.val_one, Matrix.mul_one, map_inv, Subgroup.coe_inv, mul_one, one_mul,
    Ψhat, rectangularFourierEquiv_apply,
    Units.val_mul, Matrix.mul_assoc, inverseStandardCharacter,
    MonoidHom.inv_apply, mul_assoc, mul_left_comm, mul_comm] using h

/-- Fixed-unipotent bilinear Fourier exchange in exactly the two kernel arguments. -/
theorem integral_unipotentMatrixFourierKernel_fixed
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (u : upperUnipotent (n + 1) F.Carrier) :
    (∫ X, unipotentMatrixFourierDualKernel ψ ν n Φ Ψ (u, X)
      ∂rectangularMeasure ν (n + 1) (n + 1)) =
    ∫ X, unipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ (u, X)
      ∂rectangularMeasure ν (n + 1) (n + 1) := by
  let T := F.canonicalTopologicalData
  let B := inverseTranspose (n + 1) F.Carrier u.val * weylLong (n + 1) F.Carrier
  have hu : T.determinantNorm (n + 1) u.val = 1 := by
    apply Units.ext
    apply NNReal.coe_injective
    simp only [T.determinantNorm_coe, Units.val_one, NNReal.coe_one]
    change T.normalizedAbs u.val.val.det = 1
    rw [unipotent_det, T.normalizedAbs_one]
  have hB : T.determinantNorm (n + 1) B = 1 := by
    simp only [B, map_mul, T.determinantNorm_inverseTranspose, hu, inv_one,
      T.determinantNorm_weylLong, one_mul]
  have he := (padicRectangularFourierIntegral_exchange_left F T (n + 1) (n + 1)
    ψ ν 1 B (map_one _) hB Φ Ψ).2.2
  have harg : inverseTranspose (n + 1) F.Carrier (1 * B⁻¹) =
      weylLong (n + 1) F.Carrier * u.val⁻¹ := by
    simp only [one_mul, B, map_inv, map_mul, inverseTranspose_weylLong,
      inverseTranspose_involutive, mul_inv_rev]
    rw [weylLong_inv]
  simp only [Units.val_one, Matrix.one_mul, harg] at he
  simp only [unipotentMatrixFourierDualKernel, unipotentMatrixFourierOriginalKernel,
    mul_assoc, integral_const_mul]
  exact congrArg (fun c : ℂ => (inverseStandardCharacter ψ n u : ℂ) * c) he

/-- The actual unsigned Weyl orbit Fourier exchange, with both joint
integrabilities proved before Fubini and the unchanged supplied self-dual measure. -/
theorem unipotentMatrixFourier_exchange
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΨ : tsupport (Ψ : _ → ℂ) ⊆ RankOneBox.box F A q a) :
    Integrable (unipotentMatrixFourierDualKernel ψ ν n Φ Ψ)
      ((unipotentHaar F.Carrier n).prod (rectangularMeasure ν (n + 1) (n + 1))) ∧
    Integrable (unipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ)
      ((unipotentHaar F.Carrier n).prod (rectangularMeasure ν (n + 1) (n + 1))) ∧
    (∫ z, unipotentMatrixFourierDualKernel ψ ν n Φ Ψ z
      ∂(unipotentHaar F.Carrier n).prod (rectangularMeasure ν (n + 1) (n + 1))) =
    ∫ z, unipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ z
      ∂(unipotentHaar F.Carrier n).prod (rectangularMeasure ν (n + 1) (n + 1)) := by
  have hd := integrable_unipotentMatrixFourierDualKernel F ψ ν hsd n Φ Ψ A q ha hΨ
  have ho := integrable_unipotentMatrixFourierOriginalKernel F ψ ν hsd n Φ Ψ hΦ
  refine ⟨hd, ho, ?_⟩
  rw [integral_prod _ hd, integral_prod _ ho]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (integral_unipotentMatrixFourierKernel_fixed F ψ ν n Φ Ψ)

end CanonicalPadic

end Langlands.RankinSelberg.CompactWhittakerSynthesis
