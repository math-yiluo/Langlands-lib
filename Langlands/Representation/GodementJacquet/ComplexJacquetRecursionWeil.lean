import Langlands.Representation.GodementJacquet.ComplexJacquetRecursion
import Langlands.Representation.GodementJacquet.ComplexPartialFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelQuotient
import Langlands.Global.RankinSelberg.UnfoldingSteps

/-! # Weil integration of the complex Jacquet last-column Fourier kernel -/

noncomputable section

open MeasureTheory Topology
open scoped BigOperators Matrix.Norms.Elementwise NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow lastRow_unipotent_mul unipotent_det)
open Langlands.Global.RankinSelbergGlobal hiding detPower
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "I" => Fin m
local notation "Z" => I → ℂ
local notation "H" => GeneralLinear m ℂ
local notation "G" => GeneralLinear n ℂ
local notation "U" => upperUnipotent m ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "M" => Matrix I I ℂ
local notation "R" => Matrix I (Fin n) ℂ
local notation "sm" => ((m : ℕ) : ℂ) / 2
local notation "sn" => ((n : ℕ) : ℂ) / 2

/-- The integrand of Jacquet's single smaller-group integral, with `k = h⁻¹`. -/
def complexJacquetRecursionGroupKernel (a : ℂˣ) (Φ : R → ℂ) (W : H → ℂ)
    (η : ℂˣ →* ℂˣ) (g : G) (k : H) : ℂ :=
  complexJacquetDetWeight η g sm *
    complexLastColumnFourier (-a) (fun X => Φ (X * g.val)) (k⁻¹).val (lastRow k) *
      W k * complexJacquetDetWeight η k⁻¹ (sn - 1)

private theorem complexCoordinatePair_lastRow_mulVec_inv (k : H) (z : Z) :
    complexCoordinatePair (lastRow k) ((k⁻¹).val.mulVec z) = z (Fin.last r) := by
  change (k.val.mulVec ((k⁻¹).val.mulVec z)) (Fin.last r) = _
  rw [Matrix.mulVec_mulVec, show k.val * (k⁻¹).val = 1 from k.val_inv, Matrix.one_mulVec]

private theorem integral_complexJacquet_columnChange (a : ℂˣ) (Φ : R → ℂ)
    (g : G) (k : H) (u : U) :
    (∫ z : Z, Φ ((k⁻¹).val * rectangularJoin (u⁻¹).val.val z * g.val) *
      traceCharacter a (z (Fin.last r)) ∂complexCoordinateMeasure I a) =
      detPower complexNormalizedAbs k 1 *
        complexLastColumnFourier a (fun X => Φ (X * g.val)) ((u.val * k)⁻¹).val (lastRow (u.val * k)) := by
  let ν := complexCoordinateMeasure I a
  let e := complexColumnMul k⁻¹
  let h := (u.val * k)⁻¹
  let F := fun z : Z => Φ (rectangularJoin h.val z * g.val) *
    traceCharacter a (complexCoordinatePair (lastRow (u.val * k)) z)
  have heq (z : Z) : F (e z) =
      Φ ((k⁻¹).val * rectangularJoin (u⁻¹).val.val z * g.val) *
        traceCharacter a (z (Fin.last r)) := by
    simp only [F, e, complexColumnMul_apply, lastRow_unipotent_mul,
      complexCoordinatePair_lastRow_mulVec_inv, h, mul_inv_rev, Units.val_mul, ← Subgroup.coe_inv]
    rw [rectangularJoin_left_mul]
  have hdet : (k⁻¹).val.det = k.val.det⁻¹ := by
    change ((determinant k⁻¹ : ℂˣ) : ℂ) = _
    rw [map_inv, Units.val_inv_eq_inv_val]
    rfl
  change _ = detPower complexNormalizedAbs k 1 * ∫ z, F z ∂ν
  simp_rw [← heq]
  calc
    _ = ∫ z, F z ∂ν.map e := (integral_map_equiv e.toHomeomorph.toMeasurableEquiv F).symm
    _ = _ := by
      rw [map_complexColumnMul, hdet, map_inv₀, inv_inv, integral_smul_nnreal_measure,
        NNReal.smul_def, Complex.real_smul, show (1 : ℂ) = ((1 : ℕ) : ℂ) by norm_num,
        detPower_complex_natCast, pow_one]

private theorem complexJacquetRecursionKernel_orbit (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (Φ : R → ℂ) (W : H → ℂ) (η : ℂˣ →* ℂˣ)
    (hW : ∀ (u : U) (k : H), W (u.val * k) = traceCharacter a (unipotentFourierSum r u) * W k)
    (g : G) (k : H) :
    complexJacquetRecursionKernel a D Φ W η g k =
      ∫ u : U, complexJacquetRecursionGroupKernel a Φ W η g (u.val * k) ∂D.unipotentHaar := by
  let e := upperEntryCoordinates m (K := ℂ)
  let : LocallyCompactSpace U := e.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology U := e.secondCountableTopology
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.unipotentHaar.IsInvInvariant :=
    Unfolding.isInvInvariant_of_isMulRightInvariant D.unipotentHaar
  let ν := complexCoordinateMeasure I (-a)
  let F := fun u : U => ∫ z : Z, complexJacquetRectangleKernel (-a)
    (fun X => Φ ((k⁻¹).val * X * g.val)) (u, z) ∂ν
  have hphase (u : U) :
      traceCharacter (-a) (unipotentFourierSum r u⁻¹) = traceCharacter a (unipotentFourierSum r u) := by
    rw [traceCharacter_neg_scale]
    simp only [unipotentFourierSum, UpperUnipotent.inv_adjacent_entry, Finset.sum_neg_distrib, neg_neg]
  have houter (u : U) :
      complexJacquetDetWeight η g sm * F u⁻¹ * W k * complexJacquetDetWeight η k⁻¹ sn =
        complexJacquetRecursionGroupKernel a Φ W η g (u.val * k) := by
    let h := (u.val * k)⁻¹
    have hd : determinant h = determinant k⁻¹ := by
      have hu : determinant u.val = 1 := Units.ext (unipotent_det u)
      simp only [h, map_inv, map_mul, hu, one_mul]
    have hv : h.val.det = (k⁻¹).val.det := congrArg Units.val hd
    have hweight : complexJacquetDetWeight η k⁻¹ sn * detPower complexNormalizedAbs k 1 =
        complexJacquetDetWeight η h (sn - 1) := by
      rw [sub_eq_add_neg, complexJacquetDetWeight_add, complexJacquetDetWeight,
        complexJacquetDetWeight, hd]
      have he₁ : detPower complexNormalizedAbs h sn = detPower complexNormalizedAbs k⁻¹ sn := by
        simp only [detPower, hv]
      have he₂ : detPower complexNormalizedAbs h (-1) = detPower complexNormalizedAbs k 1 := by
        rw [show detPower complexNormalizedAbs h (-1) =
          detPower complexNormalizedAbs k⁻¹ (-1) by simp only [detPower, hv],
          detPower_complex_inv, neg_neg]
      rw [he₁, he₂]
    have hF : F u⁻¹ =
        (detPower complexNormalizedAbs k 1 *
          complexLastColumnFourier (-a) (fun X => Φ (X * g.val)) h.val (lastRow (u.val * k))) *
          traceCharacter a (unipotentFourierSum r u) := by
      simp only [F, complexJacquetRectangleKernel, traceCharacter_add, ← mul_assoc, integral_mul_const,
        hphase, ν, integral_complexJacquet_columnChange, h]
    rw [hF, complexJacquetRecursionGroupKernel, hW]
    change _ = complexJacquetDetWeight η g sm *
      complexLastColumnFourier (-a) (fun X => Φ (X * g.val)) h.val (lastRow (u.val * k)) *
        (traceCharacter a (unipotentFourierSum r u) * W k) *
        complexJacquetDetWeight η h (sn - 1)
    rw [← hweight]
    ring
  change complexJacquetDetWeight η g sm * (∫ u : U, F u ∂D.unipotentHaar) *
    W k * complexJacquetDetWeight η k⁻¹ sn = _
  rw [← integral_inv_eq_self F D.unipotentHaar, ← integral_const_mul,
    ← integral_mul_const, ← integral_mul_const]
  exact integral_congr_ae (Filter.Eventually.of_forall houter)

/-- The convergent smaller-group expression (7.7) agrees with the quotient
formula (7.8) for the supplied compatible measures. -/
theorem complexJacquetRecursion_eq_integral_group (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (Φ : R → ℂ) (W : H → ℂ) (η : ℂˣ →* ℂˣ)
    (hW : ∀ (u : U) (k : H), W (u.val * k) = traceCharacter a (unipotentFourierSum r u) * W k)
    (g : G) (hI : Integrable (complexJacquetRecursionGroupKernel a Φ W η g) D.groupHaar) :
    complexJacquetRecursion a D Φ W η g =
      ∫ k : H, complexJacquetRecursionGroupKernel a Φ W η g k ∂D.groupHaar := by
  let : LocallyCompactSpace M := inferInstanceAs (LocallyCompactSpace (I → I → ℂ))
  let : SecondCountableTopology M := inferInstanceAs (SecondCountableTopology (I → I → ℂ))
  let hH := RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : SecondCountableTopology H := hH.isInducing.secondCountableTopology
  let : LocallyCompactSpace U := (upperEntryCoordinates m (K := ℂ)).isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology U := (upperEntryCoordinates m (K := ℂ)).secondCountableTopology
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  rw [← Langlands.HarishChandraSchwartz.integral_integral_out_eq
    UpperUnipotent.isClosed D.compatible hI]
  exact integral_congr_ae (Filter.Eventually.of_forall fun q =>
    complexJacquetRecursionKernel_orbit a D Φ W η hW g (q.out : H))

end Langlands.GodementJacquet
