import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockDisintegration
import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockFibers
import Langlands.Representation.RankinSelberg.TwoBlockDominantRadicalUnfolding

/-! # Original external rectangle change and exact column measures -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockFirstBlockQuotient TwoBlockLowerFirstBlockQuotient
open scoped NNReal

universe uF uW uE

section Columns

variable (K : Type uF) [MeasurableSpace K]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j : ℕ)

/-- Join the first- and second-block columns with their actual block indices. -/
def firstBlockColumnJoinEquiv :
    (Matrix (Fin j) (Fin (m 0 + 1)) K × Matrix (Fin j) (Fin (m 1 + 1)) K) ≃ᵐ
      Matrix (Fin j) (Fin (t + 1)) K :=
  (MeasurableEquiv.arrowProdEquivProdArrow
    (Fin (m 0 + 1) → K) (Fin (m 1 + 1) → K) (Fin j)).symm.trans
      (MeasurableEquiv.piCongrRight fun _ : Fin j =>
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (m 0 + 1) ⊕ Fin (m 1 + 1) => K)).symm.trans
          (MeasurableEquiv.piCongrLeft (fun _ : Fin (t + 1) => K)
            (blockCoords (blockRanks_add h))))

theorem firstBlockColumnJoinEquiv_apply
    (U : Matrix (Fin j) (Fin (m 0 + 1)) K)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K) :
    firstBlockColumnJoinEquiv K h j (U, Y) = firstBlockColumns h j U Y := by
  ext i l
  obtain ⟨l, rfl⟩ := (blockCoords (blockRanks_add h)).surjective l
  change (MeasurableEquiv.piCongrLeft (fun _ : Fin (t + 1) => K)
    (blockCoords (blockRanks_add h)))
      ((MeasurableEquiv.sumPiEquivProdPi _).symm (U i, Y i))
        (blockCoords (blockRanks_add h) l) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases l <;> simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]

theorem firstBlockColumnJoinEquiv_apply_pair
    (z : Matrix (Fin j) (Fin (m 0 + 1)) K × Matrix (Fin j) (Fin (m 1 + 1)) K) :
    firstBlockColumnJoinEquiv K h j z = firstBlockColumns h j z.1 z.2 := by
  rcases z with ⟨U, Y⟩
  exact firstBlockColumnJoinEquiv_apply K h j U Y

variable [Field K]
variable [TopologicalSpace K] (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure]

/-- The supplied scalar Haar gives the exact product of the two column blocks. -/
theorem measurePreserving_firstBlockColumnJoinEquiv :
    MeasurePreserving (firstBlockColumnJoinEquiv K h j)
      ((rectangularMeasure ν j (m 0 + 1)).prod (rectangularMeasure ν j (m 1 + 1)))
      (rectangularMeasure ν j (t + 1)) := by
  have hrow := (measurePreserving_piCongrLeft
    (fun _ : Fin (t + 1) => ν.measure) (blockCoords (blockRanks_add h))).comp
      (measurePreserving_sumPiEquivProdPi_symm
        (fun _ : Fin (m 0 + 1) ⊕ Fin (m 1 + 1) => ν.measure))
  exact (measurePreserving_pi _ _ (fun _ : Fin j => hrow)).comp
    (measurePreserving_arrowProdEquivProdArrow
      (Fin (m 0 + 1) → K) (Fin (m 1 + 1) → K) (Fin j)
      (fun _ => rowMeasure ν (m 0 + 1)) (fun _ => rowMeasure ν (m 1 + 1))).symm

/-- Product integrability is transported separately from any Bochner identity. -/
theorem integrable_firstBlockColumns_iff
    {E : Type uE} [NormedAddCommGroup E]
    (H : Matrix (Fin j) (Fin (t + 1)) K → E) :
    Integrable (fun z : Matrix (Fin j) (Fin (m 0 + 1)) K ×
        Matrix (Fin j) (Fin (m 1 + 1)) K => firstBlockColumns h j z.1 z.2 |> H)
      ((rectangularMeasure ν j (m 0 + 1)).prod (rectangularMeasure ν j (m 1 + 1))) ↔
      Integrable H (rectangularMeasure ν j (t + 1)) := by
  simpa only [Function.comp_def, firstBlockColumnJoinEquiv_apply_pair] using
    (measurePreserving_firstBlockColumnJoinEquiv K h j ν).integrable_comp_emb
      (firstBlockColumnJoinEquiv K h j).measurableEmbedding (g := H)

/-- Fubini splits the actual rectangle into its second and first column blocks. -/
theorem integral_firstBlockColumns
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Matrix (Fin j) (Fin (t + 1)) K → E)
    (hH : Integrable H (rectangularMeasure ν j (t + 1))) :
    (∫ X, H X ∂rectangularMeasure ν j (t + 1)) =
      ∫ Y, ∫ U, H (firstBlockColumns h j U Y)
        ∂rectangularMeasure ν j (m 0 + 1) ∂rectangularMeasure ν j (m 1 + 1) := by
  have hi := (integrable_firstBlockColumns_iff K h j ν H).mpr hH
  calc
    _ = ∫ z, H (firstBlockColumns h j z.1 z.2)
        ∂(rectangularMeasure ν j (m 0 + 1)).prod (rectangularMeasure ν j (m 1 + 1)) := by
      simpa only [firstBlockColumnJoinEquiv_apply_pair] using
        ((measurePreserving_firstBlockColumnJoinEquiv K h j ν).integral_comp' H).symm
    _ = _ := (integral_prod _ hi).trans (integral_integral_swap hi)

end Columns

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rectangleChangeTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance rectangleChangeValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance rectangleChangeLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance rectangleChangeCountable : SecondCountableTopology F.Carrier := F.canonicalTopologicalData.secondCountableTopology
local instance rectangleChangeMeasurable : MeasurableSpace F.Carrier := borel _
local instance rectangleChangeBorel : BorelSpace F.Carrier := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))

/-- Moving the external rectangle to the left is exactly `x = X*g`. -/
theorem unequalRankMatrix_rectangle_change
    (g : GeneralLinear (t + 1) F.Carrier)
    (X : Matrix (Fin j) (Fin (t + 1)) F.Carrier) :
    unequalRankMatrix j k g (X * g.val) =
      rectangularUnipotent j k X * appendIdentity t (j + k + 1) g := by
  simpa only [unequalRankMatrix, map_one, one_mul] using
    (unequalRankMatrix_mul_appendIdentity j k (1 : GeneralLinear (t + 1) F.Carrier) g X).symm

/-- The extra determinant power in the upper value is precisely the row scale. -/
theorem firstBlockUpperValue_eq_rowScaled (s : ℂ)
    (g : GeneralLinear (t + 1) F.Carrier)
    (X : Matrix (Fin j) (Fin (t + 1)) F.Carrier) :
    firstBlockUpperValue F h j k ell f Wtest s g X =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g (j : ℂ) *
        rectangularSectionIntegrand F ell f j k Wtest
          (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
          (X * g.val) (Quotient.mk _ g) := by
  rw [rectangularSectionIntegrand_mk, quotientDeterminantWeight_mk,
    unequalRankMatrix_rectangle_change, firstBlockUpperValue, determinantWeight_add]
  ring

/-- The original rectangle substitution cancels its exact Haar Jacobian. -/
theorem integral_firstBlockUpperValue_original (ν : AdditiveHaarMeasure F.Carrier)
    (s : ℂ) (g : GeneralLinear (t + 1) F.Carrier) :
    (∫ X, firstBlockUpperValue F h j k ell f Wtest s g X
      ∂rectangularMeasure ν j (t + 1)) =
      rectangularSectionAverage F ell f j k Wtest ν
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        (Quotient.mk _ g) := by
  simp_rw [firstBlockUpperValue_eq_rowScaled]
  rw [integral_const_mul]
  have hchange := integral_firstBlockRowChange F ν g
    (0 : Matrix (Fin 0) (Fin (t + 1)) F.Carrier)
    (0 : Matrix (Fin j) (Fin 0) F.Carrier)
    (fun x => rectangularSectionIntegrand F ell f j k Wtest
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)) x (Quotient.mk _ g))
  simp only [Matrix.zero_mul, add_zero] at hchange
  rw [hchange, NNReal.smul_def, Complex.real_smul,
    firstBlockRowJacobian F (m := fun _ : Fin 2 => t) j g,
    ← mul_assoc, ← determinantWeight_add]
  simp [rectangularSectionAverage, determinantWeight]

/-- Absolute integrability is equivalent under the original rectangle change. -/
theorem integrable_firstBlockUpperValue_original_iff (ν : AdditiveHaarMeasure F.Carrier)
    (s : ℂ) (g : GeneralLinear (t + 1) F.Carrier) :
    Integrable (fun X => firstBlockUpperValue F h j k ell f Wtest s g X)
      (rectangularMeasure ν j (t + 1)) ↔
    Integrable (fun x => rectangularSectionIntegrand F ell f j k Wtest
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)) x (Quotient.mk _ g))
      (rectangularMeasure ν j (t + 1)) := by
  simp_rw [firstBlockUpperValue_eq_rowScaled]
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (determinantWeight_ne_zero _ _ _))]
  simpa only [Matrix.zero_mul, add_zero] using
    integrable_firstBlockRowChange_iff F ν g
      (0 : Matrix (Fin 0) (Fin (t + 1)) F.Carrier)
      (0 : Matrix (Fin j) (Fin 0) F.Carrier)
      (fun x => rectangularSectionIntegrand F ell f j k Wtest
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        x (Quotient.mk _ g))

/-- The real raw-norm integral has the same exact Jacobian cancellation. -/
theorem integral_norm_firstBlockUpperValue_original (ν : AdditiveHaarMeasure F.Carrier)
    (s : ℂ) (g : GeneralLinear (t + 1) F.Carrier) :
    (∫ X, ‖firstBlockUpperValue F h j k ell f Wtest s g X‖
      ∂rectangularMeasure ν j (t + 1)) =
      rectangularSectionNormProfile F ell f j k Wtest ν
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        (Quotient.mk _ g) := by
  simp_rw [firstBlockUpperValue_eq_rowScaled, norm_mul]
  rw [integral_const_mul]
  have hchange := integral_firstBlockRowChange F ν g
    (0 : Matrix (Fin 0) (Fin (t + 1)) F.Carrier)
    (0 : Matrix (Fin j) (Fin 0) F.Carrier)
    (fun x => ‖rectangularSectionIntegrand F ell f j k Wtest
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
      x (Quotient.mk _ g)‖)
  simp only [Matrix.zero_mul, add_zero] at hchange
  rw [hchange, NNReal.smul_def, smul_eq_mul, ← mul_assoc]
  have hc :
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g (j : ℂ) *
        (((((F.canonicalTopologicalData.determinantNorm (t + 1) g : ℝ≥0) ^ j)⁻¹ :
          ℝ≥0) : ℝ) : ℂ) = 1 := by
    rw [firstBlockRowJacobian F (m := fun _ : Fin 2 => t) j g,
      ← determinantWeight_add]
    simp [determinantWeight]
  have hr := congrArg norm hc
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (NNReal.coe_nonneg _), norm_one] at hr
  rw [hr, one_mul]
  rfl

/-- Once rectangle convergence is known, splitting the columns retains the
actual original rectangle average. -/
theorem integral_firstBlockUpperValue_columns (ν : AdditiveHaarMeasure F.Carrier)
    (s : ℂ) (g : GeneralLinear (t + 1) F.Carrier)
    (hi : Integrable (fun x => rectangularSectionIntegrand F ell f j k Wtest
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
      x (Quotient.mk _ g)) (rectangularMeasure ν j (t + 1))) :
    (∫ Y, ∫ U, firstBlockUpperValue F h j k ell f Wtest s g
      (firstBlockColumns h j U Y)
        ∂rectangularMeasure ν j (m 0 + 1) ∂rectangularMeasure ν j (m 1 + 1)) =
      rectangularSectionAverage F ell f j k Wtest ν
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        (Quotient.mk _ g) := by
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hu := (integrable_firstBlockUpperValue_original_iff
    F h j k ell f Wtest ν s g).mpr hi
  exact (integral_firstBlockColumns F.Carrier h j ν _ hu).symm.trans
    (integral_firstBlockUpperValue_original F h j k ell f Wtest ν s g)

/-- The column-split raw-norm integral is the original real norm profile. -/
theorem integral_norm_firstBlockUpperValue_columns (ν : AdditiveHaarMeasure F.Carrier)
    (s : ℂ) (g : GeneralLinear (t + 1) F.Carrier)
    (hi : Integrable (fun x => rectangularSectionIntegrand F ell f j k Wtest
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
      x (Quotient.mk _ g)) (rectangularMeasure ν j (t + 1))) :
    (∫ Y, ∫ U, ‖firstBlockUpperValue F h j k ell f Wtest s g
      (firstBlockColumns h j U Y)‖
        ∂rectangularMeasure ν j (m 0 + 1) ∂rectangularMeasure ν j (m 1 + 1)) =
      rectangularSectionNormProfile F ell f j k Wtest ν
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        (Quotient.mk _ g) := by
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hu := (integrable_firstBlockUpperValue_original_iff
    F h j k ell f Wtest ν s g).mpr hi
  exact (integral_firstBlockColumns F.Carrier h j ν _ hu.norm).symm.trans
    (integral_norm_firstBlockUpperValue_original F h j k ell f Wtest ν s g)

end Padic

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
