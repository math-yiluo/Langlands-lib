import Langlands.Representation.GodementJacquet.RegularMatrixHaarDensity
import Langlands.HarmonicAnalysis.SquareFourierCrossExchange
import Langlands.Representation.GodementJacquet.InverseTransposeMatrixIntegral
import Langlands.Representation.Hecke.IntegratedConvolution
import Langlands.Representation.Character.TransportProof

/-! Actual convolution exchange for Fourier-regular matrix tests. -/

noncomputable section

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg
open scoped NNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance convolutionExchangeTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance convolutionExchangeValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance convolutionExchangeLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance convolutionExchangeT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance convolutionExchangeDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance convolutionExchangeMeasurable : MeasurableSpace F.Carrier := borel _
local instance convolutionExchangeBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance convolutionExchangeGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance convolutionExchangeGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

/-- The complementary weighted test pulled back by the actual inverse transpose. -/
def dualWeightedRegularMatrixTest (s : ℂ) :
    regularMatrixTests (K := F.Carrier) (n + 1) →ₗ[ℂ]
      SchwartzBruhat (GeneralLinear (n + 1) F.Carrier) :=
  (Hecke.TestFunction.pullback
    (GeneralLinear.inverseTransposeContinuous (n + 1) F.Carrier).toHomeomorph).toLinearMap.comp
      (weightedRegularMatrixTest F ((n + 1 : ℕ) - s))

@[simp] theorem dualWeightedRegularMatrixTest_apply (s : ℂ)
    (Φ : regularMatrixTests (K := F.Carrier) (n + 1))
    (g : GeneralLinear (n + 1) F.Carrier) :
    dualWeightedRegularMatrixTest F s Φ g =
      Φ.val (GeneralLinear.inverseTranspose (n + 1) F.Carrier g).val *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
          g (s - (n + 1 : ℕ)) := by
  change Φ.val (GeneralLinear.inverseTranspose (n + 1) F.Carrier g).val *
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
      (GeneralLinear.inverseTranspose (n + 1) F.Carrier g) ((n + 1 : ℕ) - s) = _
  rw [determinantWeight_inverseTranspose]
  congr 2
  ring

/-- Inverting an inverse transpose leaves the determinant unchanged. -/
theorem determinantWeight_inv_inverseTranspose
    (g : GeneralLinear (n + 1) F.Carrier) (s : ℂ) :
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
      (GeneralLinear.inverseTranspose (n + 1) F.Carrier g)⁻¹ s =
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s := by
  unfold determinantWeight
  change ((normalizedAbsoluteValue F.canonicalTopologicalData) g.val.transpose.det : ℂ) ^ s = _
  rw [Matrix.det_transpose]

/-- The left convolution kernel after the measure-preserving inverse transpose. -/
theorem dualWeightedRegularMatrixTest_convolution_left
    (s : ℂ) (Φ Ψ : regularMatrixTests (K := F.Carrier) (n + 1))
    (k : GeneralLinear (n + 1) F.Carrier) :
    Hecke.TestFunction.convolution (generalLinearHaar F.Carrier n)
      (dualWeightedRegularMatrixTest F s Φ) (weightedRegularMatrixTest F s Ψ) k =
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k s *
      ∫ g : GeneralLinear (n + 1) F.Carrier,
        Φ.val g.val * Ψ.val (g.val.transpose * k.val) *
          determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
            g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F.Carrier n := by
  rw [Hecke.TestFunction.convolution_apply]
  have hμ := generalLinearHaar_measurePreserving_inverseTranspose F n
  rw [← hμ.integral_comp
    (inverseTransposeMeasurableEquiv hμ.measurable).measurableEmbedding]
  calc
    _ = ∫ g : GeneralLinear (n + 1) F.Carrier,
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k s *
          (Φ.val g.val * Ψ.val (g.val.transpose * k.val) *
            determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
              g ((n + 1 : ℕ) : ℂ)) ∂generalLinearHaar F.Carrier n := by
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [dualWeightedRegularMatrixTest_apply, weightedRegularMatrixTest_apply,
        GeneralLinear.inverseTranspose_involutive, determinantWeight_inverseTranspose,
        determinantWeight_mul, determinantWeight_inv_inverseTranspose, Units.val_mul]
      change (Φ.val g.val *
          determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
            g (-(s - (n + 1 : ℕ)))) *
        (Ψ.val (g.val.transpose * k.val) *
          (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s *
            determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k s)) = _
      have hw := determinantWeight_exponent_add
        (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (-(s - (n + 1 : ℕ))) s
      rw [show -(s - (n + 1 : ℕ)) + s = ((n + 1 : ℕ) : ℂ) by ring] at hw
      rw [hw]
      ring
    _ = _ := integral_const_mul _ _

/-- The right convolution kernel expressed with the same determinant density. -/
theorem dualWeightedRegularMatrixTest_convolution_right
    (s : ℂ) (Φ Ψ : regularMatrixTests (K := F.Carrier) (n + 1))
    (k : GeneralLinear (n + 1) F.Carrier) :
    Hecke.TestFunction.convolution (generalLinearHaar F.Carrier n)
      (weightedRegularMatrixTest F s Φ) (dualWeightedRegularMatrixTest F s Ψ) k =
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
        k (s - (n + 1 : ℕ)) *
      ∫ g : GeneralLinear (n + 1) F.Carrier,
        Φ.val g.val *
          Ψ.val (g.val.transpose *
            (GeneralLinear.inverseTranspose (n + 1) F.Carrier k).val) *
          determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
            g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F.Carrier n := by
  rw [Hecke.TestFunction.convolution_apply]
  calc
    _ = ∫ g : GeneralLinear (n + 1) F.Carrier,
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
            k (s - (n + 1 : ℕ)) *
          (Φ.val g.val *
            Ψ.val (g.val.transpose *
              (GeneralLinear.inverseTranspose (n + 1) F.Carrier k).val) *
            determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
              g ((n + 1 : ℕ) : ℂ)) ∂generalLinearHaar F.Carrier n := by
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [weightedRegularMatrixTest_apply, dualWeightedRegularMatrixTest_apply,
        map_mul, map_inv, Units.val_mul, determinantWeight_mul]
      have hi (t : ℂ) :
          determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g⁻¹ t =
            determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g (-t) := by
        simpa only [determinantWeight, GeneralLinear.inverseTranspose_coe,
          Matrix.det_transpose] using
            determinantWeight_inverseTranspose
              (normalizedAbsoluteValue F.canonicalTopologicalData) g t
      rw [hi]
      change (Φ.val g.val *
          determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s) *
        (Ψ.val (g.val.transpose *
          (GeneralLinear.inverseTranspose (n + 1) F.Carrier k).val) *
          (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
              g (-(s - (n + 1 : ℕ))) *
            determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
              k (s - (n + 1 : ℕ)))) = _
      have hw := determinantWeight_exponent_add
        (normalizedAbsoluteValue F.canonicalTopologicalData) g s (-(s - (n + 1 : ℕ)))
      rw [show s + -(s - (n + 1 : ℕ)) = ((n + 1 : ℕ) : ℂ) by ring] at hw
      rw [hw]
      ring
    _ = _ := integral_const_mul _ _

/-- The Jacobian in square Fourier exchange is the negative dimension weight. -/
theorem determinantWeight_neg_dimension
    (g : GeneralLinear (n + 1) F.Carrier) :
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
        g (-((n + 1 : ℕ) : ℂ)) =
      ((((F.canonicalTopologicalData.determinantNorm (n + 1) g : ℝ≥0) ^
        (n + 1))⁻¹ : ℝ≥0) : ℂ) := by
  simp only [determinantWeight, Complex.cpow_neg, Complex.cpow_natCast,
    NNReal.coe_inv, NNReal.coe_pow, Complex.ofReal_inv, Complex.ofReal_pow]
  rfl

/-- Actual Hecke convolution exchange on tests regular on both Fourier sides. -/
theorem dualWeightedRegularMatrixTest_convolution_cross
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (s : ℂ)
    (Φ Ψ : fourierRegularMatrixTests (K := F.Carrier) (n + 1) ψ ν hsd) :
    Hecke.TestFunction.convolution (generalLinearHaar F.Carrier n)
      (dualWeightedRegularMatrixTest F s
        ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val, Φ.property.2⟩)
      (weightedRegularMatrixTest F s ⟨Ψ.val, Ψ.property.1⟩) =
    Hecke.TestFunction.convolution (generalLinearHaar F.Carrier n)
      (weightedRegularMatrixTest F s ⟨Φ.val, Φ.property.1⟩)
      (dualWeightedRegularMatrixTest F s
        ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Ψ.val, Ψ.property.2⟩) := by
  obtain ⟨c, hc, hden⟩ := exists_integral_regularMatrix_density F n ν
  apply Hecke.TestFunction.ext
  intro k
  let fL (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) : ℂ :=
    rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val X *
      Ψ.val (X.transpose * k.val)
  let fR (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) : ℂ :=
    Φ.val X * rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Ψ.val
      (X.transpose * (GeneralLinear.inverseTranspose (n + 1) F.Carrier k).val)
  have hL := hden fL (by
    intro X hX
    have hz : rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val X = 0 :=
      Φ.property.2 X hX
    simp only [fL, hz, zero_mul])
  have hR := hden fR (by
    intro X hX
    simp only [fR, Φ.property.1 X hX, zero_mul])
  have hcross :
      (∫ X, fL X ∂rectangularMeasure ν (n + 1) (n + 1)) =
        ((((F.canonicalTopologicalData.determinantNorm (n + 1) k : ℝ≥0) ^
          (n + 1))⁻¹ : ℝ≥0) : ℂ) *
          ∫ X, fR X ∂rectangularMeasure ν (n + 1) (n + 1) := by
    simpa only [fL, fR, rectangularFourierEquiv_apply] using
      padicSquareFourierIntegral_crossExchange F F.canonicalTopologicalData (n + 1)
        ψ ν k Φ.val Ψ.val
  have hc0 : (c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (ne_of_gt hc))
  apply mul_left_cancel₀ hc0
  rw [dualWeightedRegularMatrixTest_convolution_left,
    dualWeightedRegularMatrixTest_convolution_right]
  change (c : ℂ) *
      (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k s *
        ∫ g : GeneralLinear (n + 1) F.Carrier,
          fL g.val * determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
            g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F.Carrier n) =
    (c : ℂ) *
      (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
          k (s - (n + 1 : ℕ)) *
        ∫ g : GeneralLinear (n + 1) F.Carrier,
          fR g.val * determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
            g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F.Carrier n)
  calc
    _ = determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k s *
        ((c : ℂ) * ∫ g : GeneralLinear (n + 1) F.Carrier,
          fL g.val * determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
            g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F.Carrier n) := by ring
    _ = determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k s *
        ∫ X, fL X ∂rectangularMeasure ν (n + 1) (n + 1) := by rw [hL]
    _ = determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
          k (s - (n + 1 : ℕ)) *
        ∫ X, fR X ∂rectangularMeasure ν (n + 1) (n + 1) := by
      rw [hcross, ← determinantWeight_neg_dimension F k, ← mul_assoc,
        ← determinantWeight_exponent_add]
      congr 2
    _ = determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
          k (s - (n + 1 : ℕ)) *
        ((c : ℂ) * ∫ g : GeneralLinear (n + 1) F.Carrier,
          fR g.val * determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
            g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F.Carrier n) := by rw [hR]
    _ = _ := by ring

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Inverse-transpose pullback of the weighted test gives the actual zeta
operator for the representation composed with inverse transpose. -/
theorem regularMatrixZetaOperator_inverseTranspose
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsSmooth ρ)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (n + 1) F.Carrier).toMonoidHom))
    (s : ℂ) (Φ : regularMatrixTests (K := F.Carrier) (n + 1)) :
    regularMatrixZetaOperator F
      (ρ.comp (GeneralLinear.inverseTranspose (n + 1) F.Carrier).toMonoidHom)
        hι ((n + 1 : ℕ) - s) Φ =
      Hecke.integratedAction (generalLinearHaar F.Carrier n) ρ hρ
        (dualWeightedRegularMatrixTest F s Φ) := by
  ext v
  exact Character.integratedAction_comp_automorphism
    (generalLinearHaar F.Carrier n) ρ hρ
    (GeneralLinear.inverseTransposeContinuous (n + 1) F.Carrier)
    (generalLinearHaar_measurePreserving_inverseTranspose F n) hι
    (weightedRegularMatrixTest F ((n + 1 : ℕ) - s) Φ) v

/-- The actual original and transformed zeta operators satisfy the cross
identity, with composition in the order supplied by Hecke convolution. -/
theorem regularMatrixZetaOperator_inverseTranspose_cross
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsSmooth ρ)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (n + 1) F.Carrier).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (s : ℂ)
    (Φ Ψ : fourierRegularMatrixTests (K := F.Carrier) (n + 1) ψ ν hsd) :
    regularMatrixZetaOperator F
        (ρ.comp (GeneralLinear.inverseTranspose (n + 1) F.Carrier).toMonoidHom)
        hι ((n + 1 : ℕ) - s)
        ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val, Φ.property.2⟩ *
      regularMatrixZetaOperator F ρ hρ s ⟨Ψ.val, Ψ.property.1⟩ =
    regularMatrixZetaOperator F ρ hρ s ⟨Φ.val, Φ.property.1⟩ *
      regularMatrixZetaOperator F
        (ρ.comp (GeneralLinear.inverseTranspose (n + 1) F.Carrier).toMonoidHom)
        hι ((n + 1 : ℕ) - s)
        ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Ψ.val, Ψ.property.2⟩ := by
  simp_rw [regularMatrixZetaOperator_inverseTranspose F ρ hρ hι]
  ext v
  change Hecke.integratedAction (generalLinearHaar F.Carrier n) ρ hρ
      (dualWeightedRegularMatrixTest F s
        ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val, Φ.property.2⟩)
      (Hecke.integratedAction (generalLinearHaar F.Carrier n) ρ hρ
        (weightedRegularMatrixTest F s ⟨Ψ.val, Ψ.property.1⟩) v) =
    Hecke.integratedAction (generalLinearHaar F.Carrier n) ρ hρ
      (weightedRegularMatrixTest F s ⟨Φ.val, Φ.property.1⟩)
      (Hecke.integratedAction (generalLinearHaar F.Carrier n) ρ hρ
        (dualWeightedRegularMatrixTest F s
          ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Ψ.val, Ψ.property.2⟩) v)
  rw [← Hecke.integratedAction_convolution, ← Hecke.integratedAction_convolution,
    dualWeightedRegularMatrixTest_convolution_cross F ψ ν hsd s Φ Ψ]

end Langlands.GodementJacquet.Padic
