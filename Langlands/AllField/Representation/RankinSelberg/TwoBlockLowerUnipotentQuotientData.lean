import Langlands.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
/-!
# The Section 4.7 lower block-unipotent quotient and its character

JPSS (1983), Section 4.7, equation (1), printed pages 412-413: the right side is an
integral over `H_(t_1,t_2) \ G_r`, where `H_(t_1,t_2)` is the unipotent group of matrices
`[[n_1, 0], [x, n_2]]` with `n_i ∈ N_(t_i)` and arbitrary lower-left block `x`, and the
integrand involves `W(w' g)` with `w' = w_r diag(w_(t_1), w_(t_2))`.

For two blocks of sizes `m 0 + 1` and `m 1 + 1` of total rank `t + 1`, this module
constructs the matrix `C = w'` as the inverse of the published block-reversing permutation
matrix, the subgroup `H⁻ = C⁻¹ N C`, its block description, the conjugation isomorphism
`H⁻ ≃* N`, the left quotient `H⁻ \ GL_(t+1)` with its identification
`[g] ↦ [C g]` with `N \ GL_(t+1)`, the pulled-back character with its explicit block formula,
and the determinant order and slices of the quotient. No measure, integral or
convergence statement is asserted.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantSlice isClopen_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation preimage_lowerToStandard_symm_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice

open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent inducedRep_mem_compactRadicalSubmodule integral_comp_unipotentShift inverseStandardCharacter_eq_prod isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.QuotientIntegration
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uR

/-! ### The block rotation `w' = w_N diag(w_a, w_b)` -/

section Rotation



end Rotation

/-! ### The subgroup `H⁻ = C⁻¹ N C` -/

section Subgroup


end Subgroup

/-! ### Topology of the subgroup -/

section Topology


end Topology

section Canonical

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- For the canonical p-adic topology, `H⁻ ≃ₜ* N_(t+1)`. -/
def canonicalConjugationHomeomorph [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    lowerBlockUnipotent h F ≃ₜ* upperUnipotent (t + 1) F :=
  conjugationHomeomorph h F

@[simp]
theorem canonicalConjugationHomeomorph_toMulEquiv [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    (canonicalConjugationHomeomorph F h).toMulEquiv = conjugationEquiv h F :=
  rfl

/-- Continuity of `n ↦ C⁻¹ n C` on `N_(t+1)` for the canonical p-adic topology. -/
theorem continuous_conjugationEquiv_symm_canonical [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Continuous (conjugationEquiv h F).symm :=
  (canonicalConjugationHomeomorph F h).symm.continuous

/-- `H⁻` is closed in `GL_(t+1)(F)` for the canonical p-adic topology. -/
theorem isClosed_lowerBlockUnipotent_canonical [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    IsClosed (lowerBlockUnipotent h F : Set (GeneralLinear (t + 1) F)) := by
  let := (⟨⟩ : LocalFieldData F).fieldT2
  exact isClosed_lowerBlockUnipotent h F

end Canonical

/-! ### The quotient `H⁻ \ GL_(t+1)` and left multiplication by `C` -/

section Quotient


end Quotient

section FieldQuotient


end FieldQuotient

section QuotientTopology


end QuotientTopology

section QuotientCanonical

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- For the canonical p-adic topology, `H⁻ \ GL_(t+1)(F) ≃ₜ N_(t+1) \ GL_(t+1)(F)`. -/
def canonicalLowerToStandardHomeomorph [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    LowerQuotient h F ≃ₜ LeftUnipotentQuotient t F :=
  lowerToStandardHomeomorph h F

/-- `H⁻ \ GL_(t+1)(F)` is Hausdorff for the canonical p-adic topology. -/
theorem t2Space_lowerQuotient_canonical [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    T2Space (LowerQuotient h F) := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  exact leftQuotient_t2Space _ (isClosed_lowerBlockUnipotent_canonical F h)

end QuotientCanonical

/-! ### The lower character -/

section Character




end Character

section CanonicalCharacter


end CanonicalCharacter

/-! ### Determinant order and slices of the lower quotient -/

section Padic

section Determinant


end Determinant

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- `ord(det C) = 0` for the normalized order of the canonical p-adic structure. -/
theorem ord_determinant_blockRotation [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    (⟨⟩ : LocalFieldData F).ord
      (GeneralLinear.determinant (blockRotation h F) : F) = 0 := by
  have hd := determinant_blockRotation_mul_self h F
  have hm := (⟨⟩ : LocalFieldData F).ord_mul
    (GeneralLinear.determinant (blockRotation h F)).ne_zero
    (GeneralLinear.determinant (blockRotation h F)).ne_zero
  rw [hd, (⟨⟩ : LocalFieldData F).ord_one] at hm
  omega

/-- The determinant order of the lower quotient, transported through `lowerToStandard` from
the published determinant order of `N_N \ GL_N`. -/
def determinantOrder [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : LowerQuotient h F → ℤ :=
  Langlands.AllField.RankinSelberg.determinantOrder (⟨⟩ : LocalFieldData F) t ∘ lowerToStandard h F

theorem determinantOrder_apply [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (q : LowerQuotient h F) :
    determinantOrder F h q =
      Langlands.AllField.RankinSelberg.determinantOrder (⟨⟩ : LocalFieldData F) t
        (lowerToStandard h F q) :=
  rfl

/-- Representative law: the order of `[g]` is `ord(det g)`. -/
@[simp]
theorem determinantOrder_mk [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (t + 1) F) :
    determinantOrder F h (Quotient.mk _ g) =
      (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) := by
  rw [determinantOrder_apply, lowerToStandard_mk, Langlands.AllField.RankinSelberg.determinantOrder_mk, map_mul,
    Units.val_mul, (⟨⟩ : LocalFieldData F).ord_mul
      (GeneralLinear.determinant (blockRotation h F)).ne_zero
      (GeneralLinear.determinant g).ne_zero,
    ord_determinant_blockRotation, zero_add]

/-- The determinant slice of the lower quotient: the preimage under `lowerToStandard` of the
published slice of `N_N \ GL_N`. -/
def determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) : Set (LowerQuotient h F) :=
  lowerToStandard h F ⁻¹' Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t k

theorem mem_determinantSlice_iff_determinantOrder [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {k : ℤ} {q : LowerQuotient h F} :
    q ∈ determinantSlice F h k ↔ determinantOrder F h q = k :=
  Iff.rfl

/-- Representative condition for a slice: `ord(det g) = k`. -/
theorem mk_mem_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {k : ℤ} {g : GeneralLinear (t + 1) F} :
    (Quotient.mk _ g : LowerQuotient h F) ∈ determinantSlice F h k ↔
      (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) = k := by
  rw [mem_determinantSlice_iff_determinantOrder, determinantOrder_mk]

theorem preimage_lowerToStandard_symm_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) :
    (lowerToStandard h F).symm ⁻¹' determinantSlice F h k =
      Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t k := by
  rw [determinantSlice, ← Set.preimage_comp, Equiv.self_comp_symm, Set.preimage_id]

theorem continuous_determinantOrder [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Continuous (determinantOrder F h) := by
  refine (isQuotientMap_quotient_mk'
    (s := QuotientGroup.rightRel (lowerBlockUnipotent h F))).continuous_iff.mpr ?_
  change Continuous (fun g : GeneralLinear (t + 1) F =>
    determinantOrder F h (Quotient.mk _ g))
  simp only [determinantOrder_mk]
  exact (Langlands.AllField.RankinSelberg.continuous_ord_units (⟨⟩ : LocalFieldData F)).comp
    ((⟨⟩ : LocalFieldData F).generalLinearDeterminant (t + 1)).continuous

theorem isClopen_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) :
    IsClopen (determinantSlice F h k) := by
  exact (isClopen_discrete ({k} : Set ℤ)).preimage (continuous_determinantOrder F h)

theorem isOpen_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) :
    IsOpen (determinantSlice F h k) := by
  exact (isClopen_determinantSlice F h k).isOpen

/-- Every slice is measurable for any Borel structure on the lower quotient. -/
theorem measurableSet_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) :
    ∀ [MeasurableSpace (LowerQuotient h F)] [BorelSpace (LowerQuotient h F)],
      MeasurableSet (determinantSlice F h k) := by
  intro _ _
  exact (isOpen_determinantSlice F h k).measurableSet

end Padic

end Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient
