import Langlands.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
import Langlands.AllField.HarmonicAnalysis.PadicRowFourierEquivarianceProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData
/-!
# The integrand of the Section 4.7 lower unfolding

JPSS (1983), Section 4.7, equation (1), printed pages 412-413: the right side is the
integral over `H_(t_1,t_2) \ G_r` of `f[g; e, e] W(w' g) |det g|^s (gΦ)~[ζ, η]`, where
`w' = w_r diag(w_(t_1), w_(t_2))`, `ζ = (1, 0, …, 0)`, `η = (0, …, 0, 1)` and
`Φ~(ξ, v) = ∫ Φ[(w, v)] ψ(ξ ᵗw) dw` integrates the first block of a row.

For two blocks of sizes `m 0 + 1` and `m 1 + 1` of total rank `t + 1`, actual block
functionals `ℓ_i` in the inverse-character spaces, a lower normalized section `f`, a test
function `W` in the standard-character space, a Schwartz–Bruhat function `Φ` and a supplied
additive Haar measure `μ`, this module constructs the partial Fourier value
`g ↦ (gΦ)~[ζ, η]`, proves its explicit formula and the absolute integrability of its inner
integrand, and constructs the unweighted scalar function

`[g] ↦ W(C g) ⟨f(g), ⊗ ℓ_i⟩ (gΦ)~[ζ, η]`

on the published quotient `H⁻ \ GL_(t+1)`, `C = w'`, by actual quotient descent. The three
covariance laws under `H⁻` (scalar section, partial Fourier value and `W(C ·)`) and their
cancellation are proved. The weight `|det g|^s`, outer measurability, outer integrability and
the Section 4.7 identity are not part of this module.
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
open Langlands.RankinSelberg.TwoBlockLowerUnfolding hiding groupIntegrand groupIntegrand_def groupIntegrand_lowerBlockUnipotent_mul integrand integrand_mk integrand_mk_eq_groupIntegrand isTopologicalRing_carrier partialSection partialSection_apply partialSection_lowerBlockUnipotent_mul rowMeasure_map_vecMul_upperUnipotent scalarSection_lowerBlockUnipotent_mul sigmaFinite_additiveHaarMeasure whittaker_blockRotation_lowerBlockUnipotent_mul
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet hiding integrand
open Langlands.RankinSelberg.TwoBlockDeformation hiding compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent inducedRep_mem_compactRadicalSubmodule integral_comp_unipotentShift inverseStandardCharacter_eq_prod isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.QuotientIntegration
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier

universe uF uW uK uR

/-! ### The source rows `ζ` and `η` -/

section Rows


end Rows

/-! ### The row action of `H⁻` on `join (w, η)` -/

section RowAction


end RowAction

/-! ### Covariance of the scalar section and of `W(C ·)` -/

section Covariance

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F}

variable (ell : ∀ i, Whittaker.glInverseFunctionals ψ (m i) (σ i))

/-- Left translation by `u ∈ H⁻` multiplies the scalar section at the Levi identity by the
product of the two block inverse standard characters of the diagonal blocks of `u`. The
lower-left block of `u` is arbitrary; the half modulus is one because the diagonal blocks are
unipotent. -/
theorem scalarSection_lowerBlockUnipotent_mul (f : Sections F h σ)
    (u : lowerBlockUnipotent h F) (g : GeneralLinear (t + 1) F) :
    scalarSection (fun i => (ell i).val) f (u.val * g) 1 =
      (∏ i, (inverseStandardCharacter ψ (m i) (diagonalBlocks h F u i) : ℂ)) *
        scalarSection (fun i => (ell i).val) f g 1 := by
  let q : (succBlockShape m h).oppositeParabolic F :=
    Subgroup.inclusion (lowerBlockUnipotent_le_oppositeParabolic h F) u
  let b := (succBlockShape m h).oppositeLeviProjection F q
  have hcov := scalarSection_covariant (fun i => (ell i).val) f q (b := b) rfl g 1
  have hmod : (⟨⟩ : LocalFieldData F).leviHalfModulus (succBlockShape m h) b = 1 :=
    ((⟨⟩ : LocalFieldData F).leviHalfModulus_eq_one (succBlockShape m h) b).mpr
      (leviModulus_eq_one F h _ b fun i =>
        determinantNorm_eq_one_of_mem_upperUnipotent F _ (diagonalBlocks h F u i).property)
  refine hcov.trans ?_
  rw [hmod, Units.val_one, inv_one, one_mul, one_mul, scalarSection_def, scalarSection_one]
  exact tensorContraction_blockTensor F h σ ψ _ (fun i => (ell i).property) b
    (fun i => (diagonalBlocks h F u i).property) _

variable (Wtest : RankinSelberg.WhittakerFunctions ψ t)

/-- `W(C u g) = ψ_(H⁻)(u) W(C g)` for `u ∈ H⁻`: `C u C⁻¹` is upper unipotent with standard
character value the lower character of `u`. -/
theorem whittaker_blockRotation_lowerBlockUnipotent_mul (u : lowerBlockUnipotent h F)
    (g : GeneralLinear (t + 1) F) :
    Wtest.val (blockRotation h F * (u.val * g)) =
      (lowerCharacter h ψ u : ℂ) * Wtest.val (blockRotation h F * g) := by
  have e : blockRotation h F * (u.val * g) =
      (conjugationEquiv h F u).val * (blockRotation h F * g) := by
    rw [conjugationEquiv_apply_val]
    group
  rw [e]
  exact Wtest.property (conjugationEquiv h F u) (blockRotation h F * g)

end Covariance

/-! ### The partial Fourier value -/

/-- The canonical topology makes `F` a topological ring. -/
theorem isTopologicalRing_carrier (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    IsTopologicalRing F := by
  infer_instance

/-- Every additive Haar measure on `F` is σ-finite, since `F` is locally compact and second
countable. -/
theorem sigmaFinite_additiveHaarMeasure {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F]
    (μ : AdditiveHaarMeasure F) :
    SigmaFinite μ.measure := by
  have : SecondCountableTopology F :=
    Langlands.LocalFieldData.secondCountableTopology (⟨⟩ : LocalFieldData F)
  infer_instance

section PartialSection

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [MeasurableSpace F]

/-- The partial Fourier value `(gΦ)~[ζ, η]` of JPSS (4.7.1): the plus-sign first-block
integral of the row translate `x ↦ Φ(x g)` at `ξ = ζ`, second block `η`. -/
def partialSection [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F)
    (Φ : SchwartzBruhat (Fin (t + 1) → F))
    (g : GeneralLinear (t + 1) F) : ℂ :=
  letI := isTopologicalRing_carrier F
  rowPartialFourierIntegral ψ μ (succBlockEquiv h) (rowTranslate g Φ) (zeta (m 0)) (eta (m 1))

variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)
variable (μ : AdditiveHaarMeasure F)
variable (Φ : SchwartzBruhat (Fin (t + 1) → F))

/-- The explicit formula
`(gΦ)~[ζ, η] = ∫ ψ(w_0) Φ((w, η) g) dw` for the supplied product measure. -/
theorem partialSection_apply (g : GeneralLinear (t + 1) F) :
    partialSection h ψ μ Φ g =
      ∫ w, ψ.complex (w 0) *
        Φ (Matrix.vecMul (join (succBlockEquiv h) w (eta (m 1))) g.val)
          ∂rowMeasure μ (m 0 + 1) := by
  simp only [partialSection, rowPartialFourierIntegral, rowTranslate_apply, rowPairing_zeta]

end PartialSection

section Integrability

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [@BorelSpace F (⟨⟩ : LocalFieldData F).topology _]
variable (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)
variable (μ : AdditiveHaarMeasure F)
variable (Φ : SchwartzBruhat (Fin (t + 1) → F))

/-- Right multiplication by an upper unipotent matrix preserves the supplied product row
measure. -/
theorem rowMeasure_map_vecMul_upperUnipotent {d : ℕ}
    (n : upperUnipotent d F) :
    (rowMeasure μ d).map (fun x => Matrix.vecMul x (n : GeneralLinear d F).val) =
      rowMeasure μ d := by
  have := sigmaFinite_additiveHaarMeasure μ
  have : SecondCountableTopology F :=
    Langlands.LocalFieldData.secondCountableTopology (⟨⟩ : LocalFieldData F)
  have hχ (a : F) (ha : a ≠ 0) :
      μ.measure.map (fun x => a * x) =
        ((⟨⟩ : LocalFieldData F).normalizedAbsHom a)⁻¹ • μ.measure :=
    padicScalarHaarScaling F (⟨⟩ : LocalFieldData F) μ.measure (Units.mk0 a ha)
  rw [rowMeasure_map_vecMul (⟨⟩ : LocalFieldData F).normalizedAbsHom μ hχ n.val,
    RankinSelberg.unipotent_det, map_one, inv_one, one_smul]

/-- `(u g Φ)~[ζ, η] = ψ(-corner(u)) (gΦ)~[ζ, η]` for `u ∈ H⁻`: the unipotent change
`w ↦ w n_a` preserves the measure and the first coordinate, and the translation by the last
row of the lower-left block contributes the inverse corner phase. -/
theorem partialSection_lowerBlockUnipotent_mul
    (u : lowerBlockUnipotent h F) (g : GeneralLinear (t + 1) F) :
    partialSection h ψ μ Φ (u.val * g) =
      (ψ.complex (-corner h u)) *
        partialSection h ψ μ Φ g := by
  have := sigmaFinite_additiveHaarMeasure μ
  have : SecondCountableTopology F :=
    Langlands.LocalFieldData.secondCountableTopology (⟨⟩ : LocalFieldData F)
  let n := diagonalBlocks h F u 0
  let φ : (Fin (t + 1) → F) → ℂ := rowTranslate g Φ
  have hmp : MeasurePreserving
      (fun x : Fin (m 0 + 1) → F => Matrix.vecMul x (n : GeneralLinear _ F).val)
      (rowMeasure μ (m 0 + 1)) (rowMeasure μ (m 0 + 1)) :=
    ⟨(rowHomeomorph (n : GeneralLinear (m 0 + 1) F)).continuous.measurable,
      rowMeasure_map_vecMul_upperUnipotent μ n⟩
  have hemb : MeasurableEmbedding
      (fun x : Fin (m 0 + 1) → F => Matrix.vecMul x (n : GeneralLinear _ F).val) :=
    (rowHomeomorph (n : GeneralLinear (m 0 + 1) F)).measurableEmbedding
  calc partialSection h ψ μ Φ (u.val * g)
      = ∫ w, (fun x => ψ.complex (rowPairing x (zeta (m 0))) *
            φ (join (succBlockEquiv h) (x + cornerRow h u) (eta (m 1))))
          (Matrix.vecMul w (n : GeneralLinear _ F).val) ∂rowMeasure μ (m 0 + 1) := by
        simp only [partialSection, rowPartialFourierIntegral]
        congr 1
        funext w
        rw [rowTranslate_mul, rowTranslate_apply, vecMul_join_eta,
          rowPairing_vecMul_upperUnipotent_zeta]
    _ = ∫ x, ψ.complex (rowPairing x (zeta (m 0))) *
            φ (join (succBlockEquiv h) (x + cornerRow h u) (eta (m 1)))
          ∂rowMeasure μ (m 0 + 1) :=
        hmp.integral_comp hemb (fun x => ψ.complex (rowPairing x (zeta (m 0))) *
          φ (join (succBlockEquiv h) (x + cornerRow h u) (eta (m 1))))
    _ = ψ.complex (-rowPairing (cornerRow h u) (zeta (m 0))) *
          rowPartialFourierIntegral ψ μ (succBlockEquiv h) φ (zeta (m 0)) (eta (m 1)) :=
        integral_join_add ψ μ (succBlockEquiv h) φ (cornerRow h u) (zeta (m 0)) (eta (m 1))
    _ = ψ.complex (-corner h u) * partialSection h ψ μ Φ g := by
        rw [rowPairing_zeta, cornerRow_zero]
        rfl

end Integrability

/-! ### The scalar function and its descent -/

section Integrand

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F}
variable [MeasurableSpace F]
variable (ell : ∀ i, Whittaker.glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : RankinSelberg.WhittakerFunctions ψ t)
variable (Φ : SchwartzBruhat (Fin (t + 1) → F))
variable (μ : AdditiveHaarMeasure F)

/-- The unweighted scalar function `g ↦ W(C g) ⟨f(g), ⊗ ℓ_i⟩ (gΦ)~[ζ, η]` on `GL_(t+1)`,
before descent. -/
def groupIntegrand (g : GeneralLinear (t + 1) F) : ℂ :=
  Wtest.val (blockRotation h F * g) * scalarSection (fun i => (ell i).val) f g 1 *
    partialSection h ψ μ Φ g

theorem groupIntegrand_def (g : GeneralLinear (t + 1) F) :
    groupIntegrand ell f Wtest Φ μ g =
      Wtest.val (blockRotation h F * g) * scalarSection (fun i => (ell i).val) f g 1 *
        partialSection h ψ μ Φ g :=
  rfl

variable [@BorelSpace F (⟨⟩ : LocalFieldData F).topology _]

/-- Left `H⁻`-invariance: the two positive block characters and the positive corner phase of
the lower character from `W(C ·)` cancel the inverse block characters from the scalar
section and the inverse corner phase from the partial Fourier value. -/
theorem groupIntegrand_lowerBlockUnipotent_mul (u : lowerBlockUnipotent h F)
    (g : GeneralLinear (t + 1) F) :
    groupIntegrand ell f Wtest Φ μ (u.val * g) = groupIntegrand ell f Wtest Φ μ g := by
  have h0 : (standardCharacter ψ (m 0) (diagonalBlocks h F u 0) : ℂ) *
      (inverseStandardCharacter ψ (m 0) (diagonalBlocks h F u 0) : ℂ) = 1 :=
    Units.mul_inv _
  have h1 : (standardCharacter ψ (m 1) (diagonalBlocks h F u 1) : ℂ) *
      (inverseStandardCharacter ψ (m 1) (diagonalBlocks h F u 1) : ℂ) = 1 :=
    Units.mul_inv _
  have hc : ψ.complex (corner h u) * ψ.complex (-corner h u) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [groupIntegrand_def, groupIntegrand_def,
    whittaker_blockRotation_lowerBlockUnipotent_mul Wtest u g,
    scalarSection_lowerBlockUnipotent_mul ell f u g,
    partialSection_lowerBlockUnipotent_mul h ψ μ Φ u g,
    lowerCharacter_eq_diagonalBlocks, Fin.prod_univ_two]
  change (standardCharacter ψ (m 0) (diagonalBlocks h F u 0) : ℂ) *
      (standardCharacter ψ (m 1) (diagonalBlocks h F u 1) : ℂ) *
      ψ.complex (corner h u) * _ * _ * _ = _
  calc _ = ((standardCharacter ψ (m 0) (diagonalBlocks h F u 0) : ℂ) *
          (inverseStandardCharacter ψ (m 0) (diagonalBlocks h F u 0) : ℂ)) *
        ((standardCharacter ψ (m 1) (diagonalBlocks h F u 1) : ℂ) *
          (inverseStandardCharacter ψ (m 1) (diagonalBlocks h F u 1) : ℂ)) *
        (ψ.complex (corner h u) * ψ.complex (-corner h u)) *
        (Wtest.val (blockRotation h F * g) *
          scalarSection (fun i => (ell i).val) f g 1 * partialSection h ψ μ Φ g) := by ring
    _ = _ := by rw [h0, h1, hc, one_mul, one_mul, one_mul]

/-- The unweighted integrand of JPSS (4.7.1) on the actual quotient `H⁻ \ GL_(t+1)`: the
actual descent of `groupIntegrand`. No coset representative is chosen. -/
def integrand : LowerQuotient h F → ℂ :=
  descend (lowerBlockUnipotent h F) (groupIntegrand ell f Wtest Φ μ)
    (groupIntegrand_lowerBlockUnipotent_mul ell f Wtest Φ μ)

/-- Representative formula: `integrand [g] = W(C g) ⟨f(g), ⊗ ℓ_i⟩ (gΦ)~[ζ, η]`. -/
@[simp]
theorem integrand_mk (g : GeneralLinear (t + 1) F) :
    integrand ell f Wtest Φ μ (Quotient.mk _ g) =
      Wtest.val (blockRotation h F * g) * scalarSection (fun i => (ell i).val) f g 1 *
        partialSection h ψ μ Φ g :=
  rfl

theorem integrand_mk_eq_groupIntegrand (g : GeneralLinear (t + 1) F) :
    integrand ell f Wtest Φ μ (Quotient.mk _ g) = groupIntegrand ell f Wtest Φ μ g :=
  rfl

end Integrand

end Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
