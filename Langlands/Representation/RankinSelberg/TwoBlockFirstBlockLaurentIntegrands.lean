import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSections
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentFourier
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentInvolution
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-!
# The two large integrands on the first-block fibers

On the fiber `[diag(v, 1) R(y; x) g]` the upper integrand is the actual unequal-rank
integrand at `s = 0` of the right translate of the test function by `R(0; x) g` and the
first-block coefficient function of `f(g)`, times `Φ((x, η) g)`. On the fiber
`[diag(v, 1) g]` the lower integrand is the corresponding inverse half modulus times the
partial Fourier value. At the reflected point `[w v^ι]`, the transformed small integrand
of the translate by `R(0; x) g` is `ψ((x v⁻¹)_0)` times the block-rotated test value.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open MeasureTheory GeneralLinear TwoBlockJacquet TwoBlockFirstBlockQuotient
  TwoBlockLowerUnipotentQuotient TwoBlockLowerFirstBlockQuotient HarmonicAnalysis
  HarmonicAnalysis.TwoBlockRowPartialFourier QuotientIntegration Whittaker

universe uF uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {m : Fin 2 → ℕ}
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : letI := F.canonicalTopologicalData.topology
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier}

section Character

variable {t : ℕ} {h : ∑ i, (m i + 1) = t + 1}

/-- `W(C diag(v, 1) R(0; x) g) = ψ((x v⁻¹)_0) W(C diag(v, 1) g)`. -/
theorem whittaker_blockRotation_firstBlockEmbedding_lowerRadical
    (Wtest : letI := F.canonicalTopologicalData.topology
      RankinSelberg.WhittakerFunctions ψ t)
    (v : GeneralLinear (m 0 + 1) F.Carrier) (x : Fin (m 0 + 1) → F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    Wtest.val (blockRotation h F.Carrier *
        (firstBlockEmbedding h F.Carrier v * (lowerRadical h F.Carrier (rowSnoc 0 x) * g))) =
      letI := F.canonicalTopologicalData.topology
      ψ.complex (Matrix.vecMul x (v⁻¹).val 0) *
        Wtest.val (blockRotation h F.Carrier * (firstBlockEmbedding h F.Carrier v * g)) := by
  let := F.canonicalTopologicalData.topology
  let u : lowerBlockUnipotent h F.Carrier :=
    ⟨lowerRadical h F.Carrier (rowSnoc 0 x * (v⁻¹ : GeneralLinear _ F.Carrier).val),
      lowerRadical_mem h F.Carrier _⟩
  have hmul : firstBlockEmbedding h F.Carrier v * (lowerRadical h F.Carrier (rowSnoc 0 x) * g) =
      u.val * (firstBlockEmbedding h F.Carrier v * g) := by
    rw [← mul_assoc, firstBlockEmbedding_mul_lowerRadical, mul_assoc]
  have hdiag : ∀ i, diagonalBlocks h F.Carrier u i = 1 := by
    intro i
    apply Subtype.ext
    apply Units.ext
    ext a b
    rw [diagonalBlocks_apply]
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · exact lowerRadical_index_zero_zero h F.Carrier _ a b
    · exact lowerRadical_index_one_one h F.Carrier _ a b
  rw [hmul, TwoBlockLowerUnfolding.whittaker_blockRotation_lowerBlockUnipotent_mul,
    lowerCharacter_eq_diagonalBlocks, hdiag 0, hdiag 1, map_one, map_one, Units.val_one,
    one_mul, one_mul]
  congr 2
  change lowerRadical h F.Carrier _ ((succBlockShape m h).index 1 (Fin.last (m 1)))
    ((succBlockShape m h).index 0 0) = _
  rw [lowerRadical_index_one_zero, Matrix.mul_apply, rowSnoc_last]
  rfl

end Character

section Upper

variable (h : ∑ i, (m i + 1) = m 0 + (m 1 + 0 + 1) + 1)

/-- On the fiber `[diag(v, 1) R(y; x) g]`, the upper integrand is the actual unequal-rank
integrand at `s = 0` of the translate of the test function by `R(0; x) g` and the
first-block coefficient function of `f(g)`, times `Φ((x, η) g)`. -/
theorem upperIntegrand_fiberPoint_rowSnoc
    (ell : letI := F.canonicalTopologicalData.topology
      ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : letI := F.canonicalTopologicalData.topology
      RankinSelberg.WhittakerFunctions ψ (m 0 + (m 1 + 0 + 1)))
    (Φ : letI := F.canonicalTopologicalData.topology
      SchwartzBruhat (Fin (m 0 + (m 1 + 0 + 1) + 1) → F.Carrier))
    (v : GeneralLinear (m 0 + 1) F.Carrier) (y : Matrix (Fin (m 1)) (Fin (m 0 + 1)) F.Carrier)
    (x : Fin (m 0 + 1) → F.Carrier) (g : GeneralLinear (m 0 + (m 1 + 0 + 1) + 1) F.Carrier) :
    TwoBlockUnfolding.integrand ell f Wtest Φ
        (fiberPoint h F.Carrier (Quotient.mk _ v) (lowerRadical h F.Carrier (rowSnoc y x) * g)) =
      letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      unequalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData) (m 1) 0
          (translateWhittaker ψ (m 0 + (m 1 + 0 + 1)) Wtest
            (lowerRadical h F.Carrier (rowSnoc 0 x) * g))
          (firstBlockCoefficient ell f g).val 0 y (Quotient.mk _ v) *
        Φ (Matrix.vecMul (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  rw [fiberPoint_mk, TwoBlockUnfolding.integrand_mk, scalarSection_firstBlockEmbedding_mul,
    firstBlockCoefficient_lowerRadical_mul, inv_leviHalfModulus_blockPair_one,
    lastRow_firstBlockEmbedding_lowerRadical_mul, rowSnoc_last, unequalRankIntegrand_mk,
    translateWhittaker_apply, ← firstBlockEmbedding_mul_lowerRadical_rowSnoc h,
    lowerRadical_rowSnoc]
  simp only [mul_assoc, Nat.add_zero, zero_sub]
  ring

end Upper

section Lower

variable {t : ℕ} {h : ∑ i, (m i + 1) = t + 1}

/-- On the fiber `[diag(v, 1) g]`, the lower integrand is the block-rotated test value, the
inverse half modulus times the first-block coefficient, and the partial Fourier value. -/
theorem lowerIntegrand_firstBlockFiberPoint
    (ell : letI := F.canonicalTopologicalData.topology
      ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : letI := F.canonicalTopologicalData.topology
      RankinSelberg.WhittakerFunctions ψ t)
    (Φ : letI := F.canonicalTopologicalData.topology
      SchwartzBruhat (Fin (t + 1) → F.Carrier))
    (μ : letI := F.canonicalTopologicalData.topology
      letI : MeasurableSpace F.Carrier := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    (v : GeneralLinear (m 0 + 1) F.Carrier) (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    TwoBlockLowerUnfolding.integrand ell f Wtest Φ μ
        (firstBlockFiberPoint F h (Quotient.mk _ v) g) =
      Wtest.val (blockRotation h F.Carrier * (firstBlockEmbedding h F.Carrier v * g)) *
        (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
            (-(((m 1 + 1 : ℕ) : ℂ) / 2)) * (firstBlockCoefficient ell f g).val.val v) *
        (((F.canonicalTopologicalData.normalizedAbs (Matrix.det v.val))⁻¹ : ℂ) *
          ∫ x, ψ.complex (Matrix.vecMul x (v⁻¹).val 0) *
            Φ (Matrix.vecMul (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val)
            ∂rowMeasure μ (m 0 + 1)) := by
  let := F.canonicalTopologicalData.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  rw [firstBlockFiberPoint_mk, TwoBlockLowerUnfolding.integrand_mk,
    scalarSection_firstBlockEmbedding_mul, inv_leviHalfModulus_blockPair_one,
    partialSection_firstBlockEmbedding_mul]

end Lower

section Dual

variable (h : ∑ i, (m i + 1) = m 0 + (0 + m 1 + 1) + 1) (hlt : m 0 < m 0 + (0 + m 1 + 1))

/-- At the reflected point `[w v^ι]`, the transformed small integrand is the
block-rotated value `W(C diag(v, 1))` times `W'(v)` and the reflected determinant weight. -/
theorem dualIntegrand_reflectionQuotient
    (Wbig : letI := F.canonicalTopologicalData.topology
      RankinSelberg.WhittakerFunctions ψ (m 0 + (0 + m 1 + 1)))
    (Wsmall : letI := F.canonicalTopologicalData.topology
      RankinSelberg.InverseWhittakerFunctions ψ (m 0))
    (s : ℂ) (z : Matrix (Fin 0) (Fin (m 0 + 1)) F.Carrier)
    (v : GeneralLinear (m 0 + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    unequalRankIntegrand (ψ.scale (-1)) (normalizedAbsoluteValue F.canonicalTopologicalData)
        0 (m 1)
        (translateWhittaker (ψ.scale (-1)) (m 0 + (0 + m 1 + 1))
          (firstDualFunction ψ (m 0 + (0 + m 1 + 1)) Wbig)
          (blockWeylAt (m 0) (m 0 + (0 + m 1 + 1)) hlt))
        (secondDualFunction ψ (m 0) Wsmall) s z (reflectionQuotient (m 0) (Quotient.mk _ v)) =
      Wbig.val (blockRotation h F.Carrier * firstBlockEmbedding h F.Carrier v) * Wsmall.val v *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (-(s - ((0 + m 1 + 1 : ℕ) : ℂ) / 2)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have hinv : weylLong (m 0 + 1) F.Carrier * inverseTranspose (m 0 + 1) F.Carrier
      (weylLong (m 0 + 1) F.Carrier * inverseTranspose (m 0 + 1) F.Carrier v) = v := by
    rw [map_mul, inverseTranspose_weylLong, inverseTranspose_involutive, ← mul_assoc,
      weylLong_mul_self, one_mul]
  rw [reflectionQuotient_mk, unequalRankIntegrand_mk, translateWhittaker_apply,
    firstDualFunction_apply, secondDualFunction_apply,
    weylLong_mul_inverseTranspose_dualMatrix h hlt, hinv]
  congr 1
  have hr : 0 < normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det v.val) :=
    (normalizedAbsoluteValue F.canonicalTopologicalData).pos
      ((Matrix.isUnit_iff_isUnit_det _).mp v.isUnit).ne_zero
  rw [determinantWeight, determinantWeight, abv_det_weylLong_mul_inverseTranspose,
    Complex.ofReal_inv, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hr.le]
      exact Real.pi_ne_zero.symm), Complex.cpow_neg]

end Dual

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
