import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData
/-!
# The lower mixed quotient and its two fiber averages

Derived data for JPSS (1983), Section 4.9, equations (2) and (8).
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient continuous_determinantOrder continuous_firstBlockFiberPoint continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_decomposition lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurePreserving_radicalChange mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice

open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent inducedRep_mem_compactRadicalSubmodule integral_comp_unipotentShift inverseStandardCharacter_eq_prod isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk firstBlockAverage_rightTranslate isClopen_determinantSlice isClosed_mixedSubgroup measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mk_mem_determinantSlice normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF uR

section Algebra


end Algebra

section Padic

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The actual lower mixed subgroup: `R(Z) diag(a0,n)` with `|det a0| = 1` and
`n` upper unipotent. The lower-left block is unrestricted. -/
def lowerMixedSubgroup [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : Subgroup (GeneralLinear (t + 1) F) where
  carrier := {g | ∃ (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F),
    lowerProduct h F Z x.1.val x.2.val = g}
  one_mem' := ⟨0, 1, lowerProduct_one h F⟩
  mul_mem' := by
    rintro _ _ ⟨Z, x, rfl⟩ ⟨Z', x', rfl⟩
    exact ⟨Z + x.2.val.val * Z' * (x.1.val⁻¹).val, x * x',
      (lowerProduct_mul h F Z Z' x.1.val x'.1.val x.2.val x'.2.val).symm⟩
  inv_mem' := by
    rintro _ ⟨Z, x, rfl⟩
    exact ⟨-(x.2.val⁻¹).val * Z * x.1.val.val, x⁻¹,
      (lowerProduct_inv h F Z x.1.val x.2.val).symm⟩

theorem lowerProduct_mem [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F) :
    lowerProduct h F Z x.1.val x.2.val ∈ lowerMixedSubgroup F h :=
  ⟨Z, x, rfl⟩

/-- Elimination into the actual lower radical and the published mixed embedding. -/
theorem lowerMixed_decomposition [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {g : GeneralLinear (t + 1) F}
    (hg : g ∈ lowerMixedSubgroup F h) :
    ∃ (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
      (a0 : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F),
      lowerRadical h F Z * mixedEmbedding F h (a0, n) = g := by
  rcases hg with ⟨Z, x, hx⟩
  exact ⟨Z, x.1, x.2, hx⟩

/-- Intrinsic block criterion, using actual entries and the normalized absolute value
of the first diagonal determinant. Invertibility is supplied by the opposite Levi projection. -/
theorem mem_lowerMixedSubgroup_iff [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (t + 1) F) :
    g ∈ lowerMixedSubgroup F h ↔
      entryBlock h F g 0 1 = 0 ∧
      (⟨⟩ : LocalFieldData F).normalizedAbs (entryBlock h F g 0 0).det = 1 ∧
      (∀ (a b : Fin (m 1 + 1)), b < a → entryBlock h F g 1 1 a b = 0) ∧
      (∀ a : Fin (m 1 + 1), entryBlock h F g 1 1 a a = 1) := by
  constructor
  · rintro ⟨Z, x, rfl⟩
    refine ⟨entryBlock_lowerProduct_zero_one h F Z x.1.val x.2.val, ?_, ?_, ?_⟩
    · rw [entryBlock_lowerProduct_zero_zero]
      exact (mem_normOneSubgroup_iff_normalizedAbs F x.1.val).mp x.1.property
    · intro a b hab
      rw [entryBlock_lowerProduct_one_one]
      exact UpperUnipotent.entry_eq_zero x.2 hab
    · intro a
      rw [entryBlock_lowerProduct_one_one]
      exact UpperUnipotent.entry_diag x.2 a
  · rintro ⟨h01, hdet, hlow, hdiag⟩
    let gp : (succBlockShape m h).oppositeParabolic F :=
      ⟨g, mem_oppositeParabolic_of_entryBlock h F g h01⟩
    let L := (succBlockShape m h).oppositeLeviProjection F gp
    have hL0 : L 0 ∈ normOneSubgroup F (m 0 + 1) :=
      (mem_normOneSubgroup_iff_normalizedAbs F (L 0)).mpr hdet
    have hL1 : L 1 ∈ upperUnipotent (m 1 + 1) F := ⟨hlow, hdiag⟩
    exact ⟨entryBlock h F g 1 0 * ((L 0)⁻¹).val,
      (⟨L 0, hL0⟩, ⟨L 1, hL1⟩), oppositeParabolic_factorization h F gp⟩

theorem mixedSubgroup_le_lowerMixedSubgroup [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : mixedSubgroup F h ≤ lowerMixedSubgroup F h := by
  rintro _ ⟨x, rfl⟩
  exact ⟨0, x, lowerProduct_zero h F x.1.val x.2.val⟩

theorem lowerBlockUnipotent_le_lowerMixedSubgroup [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    lowerBlockUnipotent h F ≤ lowerMixedSubgroup F h := by
  intro g hg
  have hc := (mem_lowerBlockUnipotent_iff h F g).mp hg
  apply (mem_lowerMixedSubgroup_iff F h g).mpr
  refine ⟨?_, ?_, hc.2.1 1, hc.2.2 1⟩
  · ext a b
    exact hc.1 a b
  · let n := diagonalBlocks h F ⟨g, hg⟩ 0
    exact (mem_normOneSubgroup_iff_normalizedAbs F n.val).mp
      (determinantNorm_eq_one_of_mem_upperUnipotent F (⟨⟩ : LocalFieldData F) n.property)

theorem lowerMixedSubgroup_le_oppositeParabolic [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    lowerMixedSubgroup F h ≤ (succBlockShape m h).oppositeParabolic F := by
  intro g hg
  exact mem_oppositeParabolic_of_entryBlock h F g
    ((mem_lowerMixedSubgroup_iff F h g).mp hg).1

theorem lowerMixedSubgroup_le_normOneSubgroup [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    lowerMixedSubgroup F h ≤ normOneSubgroup F (t + 1) := by
  rintro _ ⟨Z, x, rfl⟩
  change (⟨⟩ : LocalFieldData F).normalizedAbsUnits
    (GeneralLinear.determinant (lowerProduct h F Z x.1.val x.2.val)) = 1
  change (⟨⟩ : LocalFieldData F).normalizedAbsUnits
    (GeneralLinear.determinant (lowerRadical h F Z * mixedEmbedding F h x)) = 1
  rw [map_mul, determinant_lowerRadical, one_mul, determinant_mixedEmbedding]
  exact x.1.property

/-- The first diagonal block is invertible, with its actual inverse extracted by the
opposite Levi projection; its determinant has absolute value one. -/
def lowerMixedDiagonal [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : lowerMixedSubgroup F h) :
    normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F :=
  (⟨(succBlockShape m h).oppositeLeviProjection F
      ⟨g.val, lowerMixedSubgroup_le_oppositeParabolic F h g.property⟩ 0,
    (mem_normOneSubgroup_iff_normalizedAbs F _).mpr
      ((mem_lowerMixedSubgroup_iff F h g.val).mp g.property).2.1⟩,
   ⟨(succBlockShape m h).oppositeLeviProjection F
      ⟨g.val, lowerMixedSubgroup_le_oppositeParabolic F h g.property⟩ 1,
    ⟨((mem_lowerMixedSubgroup_iff F h g.val).mp g.property).2.2.1,
      ((mem_lowerMixedSubgroup_iff F h g.val).mp g.property).2.2.2⟩⟩)

@[simp]
theorem lowerMixedDiagonal_fst_val [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : lowerMixedSubgroup F h) :
    (lowerMixedDiagonal F h g).1.val.val = entryBlock h F g.val 0 0 := rfl

@[simp]
theorem lowerMixedDiagonal_snd_val [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : lowerMixedSubgroup F h) :
    (lowerMixedDiagonal F h g).2.val.val = entryBlock h F g.val 1 1 := rfl

/-- Coordinates `(X * a0⁻¹, (a0,n))` of the actual block matrix `[[a0,0],[X,n]]`. -/
def lowerMixedCoordinates [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : lowerMixedSubgroup F h) :
    Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
      (normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F) :=
  (entryBlock h F g.val 1 0 * ((lowerMixedDiagonal F h g).1.val⁻¹).val,
    lowerMixedDiagonal F h g)

@[simp]
theorem lowerMixedDiagonal_lowerProduct [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F) :
    lowerMixedDiagonal F h ⟨lowerProduct h F Z x.1.val x.2.val,
      lowerProduct_mem F h Z x⟩ = x := by
  refine Prod.ext (Subtype.ext (Matrix.GeneralLinearGroup.ext fun a b => ?_))
    (Subtype.ext (Matrix.GeneralLinearGroup.ext fun a b => ?_))
  · exact congrFun₂ (entryBlock_lowerProduct_zero_zero h F Z x.1.val x.2.val) a b
  · exact congrFun₂ (entryBlock_lowerProduct_one_one h F Z x.1.val x.2.val) a b

@[simp]
theorem lowerMixedCoordinates_lowerProduct [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F) :
    lowerMixedCoordinates F h ⟨lowerProduct h F Z x.1.val x.2.val,
      lowerProduct_mem F h Z x⟩ = (Z, x) := by
  simp [lowerMixedCoordinates, Matrix.mul_assoc]

/-- Reconstructing from the coordinates returns the original matrix. -/
theorem lowerProduct_lowerMixedCoordinates [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : lowerMixedSubgroup F h) :
    lowerProduct h F (lowerMixedCoordinates F h g).1
      (lowerMixedCoordinates F h g).2.1.val (lowerMixedCoordinates F h g).2.2.val = g.val :=
  oppositeParabolic_factorization h F
    ⟨g.val, lowerMixedSubgroup_le_oppositeParabolic F h g.property⟩

/-- The coordinate equivalence, before topology. Its domain is given the semidirect
multiplication stated below, rather than the product group multiplication. -/
def lowerMixedSubgroupEquiv [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
      (normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F) ≃
        lowerMixedSubgroup F h where
  toFun x := ⟨lowerProduct h F x.1 x.2.1.val x.2.2.val, lowerProduct_mem F h x.1 x.2⟩
  invFun := lowerMixedCoordinates F h
  left_inv x := lowerMixedCoordinates_lowerProduct F h x.1 x.2
  right_inv g := Subtype.ext (lowerProduct_lowerMixedCoordinates F h g)

@[simp]
theorem lowerMixedSubgroupEquiv_apply_val [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (x : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
      (normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F)) :
    (lowerMixedSubgroupEquiv F h x).val = lowerRadical h F x.1 * mixedEmbedding F h x.2 :=
  rfl

/-- The coordinate equivalence is a homeomorphism in the canonical topology. -/
def lowerMixedSubgroupHomeomorph [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
      (normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F) ≃ₜ
        lowerMixedSubgroup F h := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hd : Continuous (lowerMixedDiagonal F h) := by
    have hp : Continuous (fun g : lowerMixedSubgroup F h =>
        (succBlockShape m h).oppositeLeviProjection F
          ⟨g.val, lowerMixedSubgroup_le_oppositeParabolic F h g.property⟩) :=
      ((succBlockShape m h).oppositeLeviProjectionContinuous F).continuous.comp
        (continuous_subtype_val.subtype_mk _)
    exact (((continuous_apply 0).comp hp).subtype_mk _).prodMk
      (((continuous_apply 1).comp hp).subtype_mk _)
  refine
    { toEquiv := lowerMixedSubgroupEquiv F h
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact ((continuous_lowerProduct h F).comp
      (continuous_fst.prodMk
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
          (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))).subtype_mk _
  · exact (((continuous_entryBlock h F 1 0).comp continuous_subtype_val).matrix_mul
      (Units.continuous_val.comp
        ((continuous_subtype_val.comp (continuous_fst.comp hd)).inv))).prodMk hd

/-- Closedness follows from the actual upper-right block, first determinant and
upper-unipotent second block conditions. -/
theorem isClosed_lowerMixedSubgroup [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    IsClosed (lowerMixedSubgroup F h : Set (GeneralLinear (t + 1) F)) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  have he : (lowerMixedSubgroup F h : Set (GeneralLinear (t + 1) F)) =
      {g | entryBlock h F g 0 1 = 0} ∩
      ({g | T.normalizedAbs (entryBlock h F g 0 0).det = 1} ∩
      ((⋂ (a : Fin (m 1 + 1)) (b : Fin (m 1 + 1)) (_ : b < a),
        {g | entryBlock h F g 1 1 a b = 0}) ∩
      (⋂ (a : Fin (m 1 + 1)), {g | entryBlock h F g 1 1 a a = 1}))) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_lowerMixedSubgroup_iff F h g
  have hentry : ∀ (a b : Fin (m 1 + 1)) (c : F),
      IsClosed {g : GeneralLinear (t + 1) F | entryBlock h F g 1 1 a b = c} :=
    fun a b c => isClosed_eq (GeneralLinear.entry (R := F) _ _).continuous continuous_const
  rw [he]
  exact (isClosed_eq (continuous_entryBlock h F 0 1) continuous_const).inter
    ((isClosed_eq (T.continuous_normalizedAbs.comp
      (continuous_entryBlock h F 0 0).matrix_det) continuous_const).inter
      ((isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
        hentry a b 0).inter (isClosed_iInter fun a => hentry a a 1)))

/-- The first inverse diagonal coordinate is the actual first entry block. -/
theorem lowerMixedSubgroupEquiv_symm_apply_fst [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : lowerMixedSubgroup F h) :
    ((lowerMixedSubgroupEquiv F h).symm g).2.1.val.val =
      entryBlock h F g.val 0 0 := rfl

/-- Coordinate multiplication is semidirect: `Z + n Z2 a0⁻¹` on the rectangle. -/
theorem lowerMixedSubgroupEquiv_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (x y : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
      (normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F)) :
    lowerMixedSubgroupEquiv F h x * lowerMixedSubgroupEquiv F h y =
      lowerMixedSubgroupEquiv F h
        (x.1 + x.2.2.val.val * y.1 * (x.2.1.val⁻¹).val, x.2 * y.2) :=
  Subtype.ext (lowerProduct_mul h F x.1 y.1 x.2.1.val y.2.1.val x.2.2.val y.2.2.val)

/-- The actual left quotient by the lower mixed subgroup. -/
abbrev LowerMixedQuotient [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] := LeftQuotient (lowerMixedSubgroup F h)

/-- Projection from the published diagonal mixed quotient, by actual quotient descent. -/
def projectionFromMixed [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : MixedQuotient F h → LowerMixedQuotient F h :=
  descend _ (fun g => (Quotient.mk _ g : LowerMixedQuotient F h))
    (fun u g => TwoBlockUnipotentQuotient.mk_mul_of_mem _
      (mixedSubgroup_le_lowerMixedSubgroup F h u.property) g)

/-- Projection from the published lower unipotent quotient, by actual quotient descent. -/
def projectionFromLower [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : LowerQuotient h F → LowerMixedQuotient F h :=
  descend _ (fun g => (Quotient.mk _ g : LowerMixedQuotient F h))
    (fun u g => TwoBlockUnipotentQuotient.mk_mul_of_mem _
      (lowerBlockUnipotent_le_lowerMixedSubgroup F h u.property) g)

@[simp]
theorem projectionFromMixed_mk [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (t + 1) F) :
    projectionFromMixed F h (Quotient.mk _ g) = Quotient.mk _ g := rfl

@[simp]
theorem projectionFromLower_mk [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (t + 1) F) :
    projectionFromLower F h (Quotient.mk _ g) = Quotient.mk _ g := rfl

theorem continuous_projectionFromMixed [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Continuous (projectionFromMixed F h) := by
  exact Continuous.quotient_lift continuous_quotient_mk' _

theorem continuous_projectionFromLower [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Continuous (projectionFromLower F h) := by
  exact Continuous.quotient_lift continuous_quotient_mk' _

/-- The determinant order descends because the lower mixed subgroup lies in `GL^0`. -/
def determinantOrder [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : LowerMixedQuotient F h → ℤ :=
  descend _
    (fun g => (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F))
    (fun l g => by
      rw [map_mul, Units.val_mul,
        (⟨⟩ : LocalFieldData F).ord_mul (GeneralLinear.determinant l.val).ne_zero
          (GeneralLinear.determinant g).ne_zero,
        ord_determinant_eq_zero F (lowerMixedSubgroup_le_normOneSubgroup F h l.property), zero_add])

@[simp]
theorem determinantOrder_mk [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (t + 1) F) :
    determinantOrder F h (Quotient.mk _ g) =
      (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) := rfl

theorem continuous_determinantOrder [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Continuous (determinantOrder F h) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  exact Continuous.quotient_lift
    ((continuous_ord_units T).comp (T.generalLinearDeterminant (t + 1)).continuous) _

/-- Integer determinant slices. The source's `Lminus \ G^0` is precisely slice zero. -/
def determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) : Set (LowerMixedQuotient F h) :=
  {q | determinantOrder F h q = k}

theorem mk_mem_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {k : ℤ} {g : GeneralLinear (t + 1) F} :
    (Quotient.mk _ g : LowerMixedQuotient F h) ∈ determinantSlice F h k ↔
      (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) = k := Iff.rfl

theorem isClopen_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) :
    IsClopen (determinantSlice F h k) := by
  exact (isClopen_discrete ({k} : Set ℤ)).preimage (continuous_determinantOrder F h)

theorem measurableSet_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) :
    ∀ [MeasurableSpace (LowerMixedQuotient F h)] [BorelSpace (LowerMixedQuotient F h)],
      MeasurableSet (determinantSlice F h k) := by
  intro _ _
  exact (isClopen_determinantSlice F h k).isOpen.measurableSet

/-- Both projections preserve the determinant order. -/
@[simp]
theorem determinantOrder_projectionFromMixed [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (q : MixedQuotient F h) :
    determinantOrder F h (projectionFromMixed F h q) =
      Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantOrder F h q := by
  induction q using Quotient.inductionOn with
  | h g => rfl

@[simp]
theorem determinantOrder_projectionFromLower [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (q : LowerQuotient h F) :
    determinantOrder F h (projectionFromLower F h q) =
      Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder F h q := by
  induction q using Quotient.inductionOn with
  | h g => exact (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder_mk F h g).symm

theorem projectionFromMixed_preimage_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) :
    projectionFromMixed F h ⁻¹' determinantSlice F h k =
      Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantSlice F h k := by
  ext q
  change determinantOrder F h (projectionFromMixed F h q) = k ↔
    Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantOrder F h q = k
  rw [determinantOrder_projectionFromMixed]

theorem projectionFromLower_preimage_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) :
    projectionFromLower F h ⁻¹' determinantSlice F h k =
      Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k := by
  ext q
  change determinantOrder F h (projectionFromLower F h q) = k ↔
    Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder F h q = k
  rw [determinantOrder_projectionFromLower]

end Padic

/-! ### Commutation of the lower radical with block-diagonal matrices -/

section Commutation


end Commutation

/-! ### Rectangular fibers into the mixed quotient -/

section RadicalFiber

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The rectangular fiber map `(Z, g) ↦ [R(Z) g]_M` into the published mixed quotient
`M \ G`, `M = diag(GL_a^0, N_b)`. -/
def radicalFiberPoint [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (g : GeneralLinear (t + 1) F) : MixedQuotient F h :=
  Quotient.mk _ (lowerRadical h F Z * g)

theorem radicalFiberPoint_def [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (g : GeneralLinear (t + 1) F) :
    radicalFiberPoint F h Z g = Quotient.mk _ (lowerRadical h F Z * g) :=
  rfl

/-- The rectangular fiber map is jointly continuous in `(Z, g)`. -/
theorem continuous_radicalFiberPoint [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Continuous (Function.uncurry (radicalFiberPoint F h)) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (t + 1)
  exact continuous_quotient_mk'.comp
    (((continuous_lowerRadical h F).comp continuous_fst).mul continuous_snd)

/-- Since `det R(Z) = 1`, the fiber point has the determinant order of `g`. -/
@[simp]
theorem determinantOrder_radicalFiberPoint [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (g : GeneralLinear (t + 1) F) :
    Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantOrder F h (radicalFiberPoint F h Z g) =
      (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) := by
  rw [radicalFiberPoint_def, Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantOrder_mk, map_mul,
    determinant_lowerRadical, one_mul]

/-- The fiber point lies in the published slice `M \ G^k` exactly when `ord(det g) = k`. -/
theorem radicalFiberPoint_mem_determinantSlice_iff [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (g : GeneralLinear (t + 1) F) (k : ℤ) :
    radicalFiberPoint F h Z g ∈ Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantSlice F h k ↔
      (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) = k := by
  rw [Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mem_determinantSlice, determinantOrder_radicalFiberPoint]

/-- The affine change of rectangular coordinates `Z ↦ n⁻¹ (Z + Z0) a0` attached to
`l = R(Z0) D(a0, n)`. -/
def radicalChange [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {a b : ℕ} (Z0 : Matrix (Fin b) (Fin a) F) (a0 : normOneSubgroup F a)
    (n : upperUnipotent b F) (Z : Matrix (Fin b) (Fin a) F) :
    Matrix (Fin b) (Fin a) F :=
  (n.val⁻¹).val * (Z + Z0) * a0.val.val

theorem radicalChange_apply [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {a b : ℕ} (Z0 : Matrix (Fin b) (Fin a) F)
    (a0 : normOneSubgroup F a) (n : upperUnipotent b F)
    (Z : Matrix (Fin b) (Fin a) F) :
    radicalChange F Z0 a0 n Z = (n.val⁻¹).val * (Z + Z0) * a0.val.val :=
  rfl

/-- Representative change: for `l = R(Z0) D(a0, n)`,
`radicalFiberPoint Z (l g) = radicalFiberPoint (n⁻¹ (Z + Z0) a0) g`. -/
theorem radicalFiberPoint_lowerRadical_mixedEmbedding_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (Z Z0 : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (a0 : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F)
    (g : GeneralLinear (t + 1) F) :
    radicalFiberPoint F h Z (lowerRadical h F Z0 * mixedEmbedding F h (a0, n) * g) =
      radicalFiberPoint F h (radicalChange F Z0 a0 n Z) g := by
  rw [radicalFiberPoint_def, radicalFiberPoint_def, ← mul_assoc, ← mul_assoc,
    ← lowerRadical_add, mixedEmbedding_apply, lowerRadical_mul_leviEmbedding_blockPair,
    mul_assoc]
  exact TwoBlockUnipotentQuotient.mk_mul_of_mem _ (mixedEmbedding_mem F h (a0, n)) _

/-- The affine change is a homeomorphism of the rectangle. -/
def radicalChangeHomeomorph [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {a b : ℕ} (Z0 : Matrix (Fin b) (Fin a) F)
    (a0 : normOneSubgroup F a) (n : upperUnipotent b F) :
    Matrix (Fin b) (Fin a) F ≃ₜ Matrix (Fin b) (Fin a) F := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact
    { toFun := radicalChange F Z0 a0 n
      invFun := fun W => n.val.val * W * (a0.val⁻¹).val - Z0
      left_inv := fun Z => by
        simp only [radicalChange, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, add_sub_cancel_right]
      right_inv := fun W => by
        simp only [radicalChange, sub_add_cancel, Matrix.mul_assoc, Units.inv_mul,
          Matrix.mul_one]
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      continuous_toFun :=
        (continuous_const.matrix_mul (continuous_id.add continuous_const)).matrix_mul
          continuous_const
      continuous_invFun :=
        ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).sub
          continuous_const }

@[simp]
theorem radicalChangeHomeomorph_apply [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {a b : ℕ} (Z0 : Matrix (Fin b) (Fin a) F)
    (a0 : normOneSubgroup F a) (n : upperUnipotent b F)
    (Z : Matrix (Fin b) (Fin a) F) :
    radicalChangeHomeomorph F Z0 a0 n Z = radicalChange F Z0 a0 n Z :=
  rfl

/-- The affine change `Z ↦ n⁻¹ (Z + Z0) a0` preserves every Borel additive Haar measure on
the rectangle: its linear part has both determinant norms one
(`padicRectangularHaarScaling`), and the translation part preserves Haar measure. -/
theorem measurePreserving_radicalChange [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {a b : ℕ} :
    ∀ [MeasurableSpace (Matrix (Fin b) (Fin a) F)]
      [BorelSpace (Matrix (Fin b) (Fin a) F)]
      (μR : Measure (Matrix (Fin b) (Fin a) F)) [μR.IsAddHaarMeasure]
      (Z0 : Matrix (Fin b) (Fin a) F) (a0 : normOneSubgroup F a)
      (n : upperUnipotent b F),
      MeasurePreserving (radicalChange F Z0 a0 n) μR μR := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μR _ Z0 a0 n
  have hlin : Continuous (fun X : Matrix (Fin b) (Fin a) F =>
      (n.val⁻¹).val * X * a0.val.val) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have htr : Continuous (fun Z : Matrix (Fin b) (Fin a) F => Z + Z0) :=
    continuous_id.add continuous_const
  have hn : T.determinantNorm b n.val = 1 :=
    determinantNorm_eq_one_of_mem_upperUnipotent F T n.property
  have ha : T.determinantNorm a a0.val = 1 := (mem_normOneSubgroup_iff F a0.val).mp a0.property
  have hscale := Langlands.AllField.HarmonicAnalysis.padicRectangularHaarScaling F T b a μR n.val⁻¹ a0.val⁻¹
  simp only [inv_inv, map_inv, hn, ha, inv_one, Units.val_one, one_pow, div_one,
    one_smul] at hscale
  refine ⟨hlin.measurable.comp htr.measurable, ?_⟩
  change μR.map ((fun X : Matrix (Fin b) (Fin a) F => (n.val⁻¹).val * X * a0.val.val) ∘
    (fun Z => Z + Z0)) = μR
  rw [← Measure.map_map hlin.measurable htr.measurable, map_add_right_eq_self μR Z0, hscale]

/-- Integrals over the rectangle are invariant under the affine change, with no
integrability hypothesis. -/
theorem integral_comp_radicalChange [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {a b : ℕ} :
    ∀ [MeasurableSpace (Matrix (Fin b) (Fin a) F)]
      [BorelSpace (Matrix (Fin b) (Fin a) F)]
      (μR : Measure (Matrix (Fin b) (Fin a) F)) [μR.IsAddHaarMeasure]
      (Z0 : Matrix (Fin b) (Fin a) F) (a0 : normOneSubgroup F a)
      (n : upperUnipotent b F) (G : Matrix (Fin b) (Fin a) F → ℂ),
      ∫ Z, G (radicalChange F Z0 a0 n Z) ∂μR = ∫ Z, G Z ∂μR := by
  intro _ _ μR _ Z0 a0 n G
  exact (measurePreserving_radicalChange F μR Z0 a0 n).integral_comp
    (radicalChangeHomeomorph F Z0 a0 n).measurableEmbedding G

section Average

variable [MeasurableSpace (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)]

/-- The rectangular fiber integral `g ↦ ∫ f([R(Z) g]_M) dμR(Z)`, the ordinary total Bochner
integral against the supplied measure on the rectangle. -/
def radicalFiberIntegral [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F))
    (f : MixedQuotient F h → ℂ) (g : GeneralLinear (t + 1) F) : ℂ :=
  ∫ Z, f (radicalFiberPoint F h Z g) ∂μR

theorem radicalFiberIntegral_def [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F))
    (f : MixedQuotient F h → ℂ) (g : GeneralLinear (t + 1) F) :
    radicalFiberIntegral F h μR f g = ∫ Z, f (radicalFiberPoint F h Z g) ∂μR :=
  rfl

/-- Left invariance under `l = R(Z0) D(a0, n)`, for every Borel additive Haar measure and
every scalar function, without any integrability hypothesis. -/
theorem radicalFiberIntegral_lowerRadical_mixedEmbedding_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ [BorelSpace (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)]
      (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)) [μR.IsAddHaarMeasure]
      (f : MixedQuotient F h → ℂ) (Z0 : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
      (a0 : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F)
      (g : GeneralLinear (t + 1) F),
      radicalFiberIntegral F h μR f
          (lowerRadical h F Z0 * mixedEmbedding F h (a0, n) * g) =
        radicalFiberIntegral F h μR f g := by
  intro _ μR _ f Z0 a0 n g
  simp only [radicalFiberIntegral_def, radicalFiberPoint_lowerRadical_mixedEmbedding_mul]
  exact integral_comp_radicalChange F μR Z0 a0 n (fun Z => f (radicalFiberPoint F h Z g))

/-- Left invariance under every element of the actual lower mixed subgroup. -/
theorem radicalFiberIntegral_lowerMixedSubgroup_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ [BorelSpace (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)]
      (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)) [μR.IsAddHaarMeasure]
      (f : MixedQuotient F h → ℂ) (l : lowerMixedSubgroup F h)
      (g : GeneralLinear (t + 1) F),
      radicalFiberIntegral F h μR f (l.val * g) = radicalFiberIntegral F h μR f g := by
  intro _ μR _ f l g
  obtain ⟨Z0, a0, n, hl⟩ := lowerMixed_decomposition F h l.property
  rw [← hl]
  exact radicalFiberIntegral_lowerRadical_mixedEmbedding_mul F h μR f Z0 a0 n g

/-- The rectangular average on the actual quotient `Lminus \ G`: the actual descent of the
left-`Lminus`-invariant fiber integral. No coset representative is chosen. -/
def radicalAverage [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ [BorelSpace (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)]
      (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)) [μR.IsAddHaarMeasure],
      (MixedQuotient F h → ℂ) → LowerMixedQuotient F h → ℂ := by
  intro _ μR _ f
  exact descend _ (radicalFiberIntegral F h μR f)
    (fun l g => radicalFiberIntegral_lowerMixedSubgroup_mul F h μR f l g)

/-- Representative evaluation of the rectangular average. -/
theorem radicalAverage_mk [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ [BorelSpace (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)]
      (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)) [μR.IsAddHaarMeasure]
      (f : MixedQuotient F h → ℂ) (g : GeneralLinear (t + 1) F),
      radicalAverage F h μR f (Quotient.mk _ g) = ∫ Z, f (radicalFiberPoint F h Z g) ∂μR := by
  intro _ μR _ f g
  rfl

end Average

end RadicalFiber

/-! ### First-block fibers into the lower unipotent quotient -/

section FirstBlockFiber

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The first-block fiber map `([v], g) ↦ [I(v) g]_{H⁻}` from the small quotient
`N_a \ GL_a` to `H⁻ \ G`, by actual quotient descent: left multiplication of `v` by
`n ∈ N_a` multiplies `I(v) g` on the left by `I(n) ∈ H⁻`. -/
def firstBlockFiberPoint (q : LeftUnipotentQuotient (m 0) F)
    (g : GeneralLinear (t + 1) F) : LowerQuotient h F :=
  descend _
    (fun v => (Quotient.mk _ (firstBlockEmbedding h F v * g) : LowerQuotient h F))
    (fun n v => by
      rw [map_mul, mul_assoc]
      exact TwoBlockUnipotentQuotient.mk_mul_of_mem _
        (firstBlockEmbedding_mem_lowerBlockUnipotent h F n.property) _)
    q

/-- Representative formula: `firstBlockFiberPoint [v] g = [I(v) g]_{H⁻}`. -/
@[simp]
theorem firstBlockFiberPoint_mk (v : GeneralLinear (m 0 + 1) F)
    (g : GeneralLinear (t + 1) F) :
    firstBlockFiberPoint F h (Quotient.mk _ v) g =
      Quotient.mk _ (firstBlockEmbedding h F v * g) :=
  rfl

/-- The first-block fiber map is jointly continuous in `(q, g)`. -/
theorem continuous_firstBlockFiberPoint [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Continuous (Function.uncurry (firstBlockFiberPoint F h)) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let := T.generalLinearTopologicalGroup (t + 1)
  have hq : IsOpenQuotientMap (Prod.map (leftQuotientMap (upperUnipotent (m 0 + 1) F))
      (id : GeneralLinear (t + 1) F → GeneralLinear (t + 1) F)) :=
    (leftQuotient_isOpenQuotientMap _).prodMap IsOpenQuotientMap.id
  rw [← hq.continuous_comp_iff]
  have he : Function.uncurry (firstBlockFiberPoint F h) ∘
      Prod.map (leftQuotientMap (upperUnipotent (m 0 + 1) F)) id =
      fun x : GeneralLinear (m 0 + 1) F × GeneralLinear (t + 1) F =>
        (Quotient.mk _ (firstBlockEmbedding h F x.1 * x.2) :
          LowerQuotient h F) :=
    rfl
  rw [he]
  exact continuous_quotient_mk'.comp
    (((continuous_firstBlockEmbedding h F).comp continuous_fst).mul continuous_snd)

/-- The block identity `I(v) R(Z0) D(a0, n) = R(Z0 v⁻¹) diag(1, n) I(v a0)`. -/
theorem firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (v : GeneralLinear (m 0 + 1) F)
    (Z0 : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (a0 : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F) :
    firstBlockEmbedding h F v * (lowerRadical h F Z0 * mixedEmbedding F h (a0, n)) =
      lowerRadical h F (Z0 * (v⁻¹ : GeneralLinear _ F).val) *
          (succBlockShape m h).leviEmbedding F (blockPair F (1, n.val)) *
        firstBlockEmbedding h F (v * a0.val) := by
  rw [← mul_assoc, firstBlockEmbedding_mul_lowerRadical, mul_assoc, mixedEmbedding_apply,
    firstBlockEmbedding_mul_leviEmbedding_blockPair, ← mul_assoc]

/-- The first two factors `R(Z0 v⁻¹) diag(1, n)` of the block identity lie in `H⁻`. -/
theorem lowerRadical_mul_leviEmbedding_one_mem
    (W : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (n : upperUnipotent (m 1 + 1) F) :
    lowerRadical h F W *
        (succBlockShape m h).leviEmbedding F (blockPair F (1, n.val)) ∈
      lowerBlockUnipotent h F :=
  (lowerBlockUnipotent h F).mul_mem (lowerRadical_mem h F W)
    (leviEmbedding_blockPair_mem_lowerBlockUnipotent h F
      (upperUnipotent (m 0 + 1) F).one_mem n.property)

/-- Change of fiber: for `l = R(Z0) D(a0, n)`, left multiplication of the base point by `l`
is right translation of the small quotient by `a0`. -/
theorem firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (m 0 + 1)
    ∀ (q : LeftUnipotentQuotient (m 0) F)
      (Z0 : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
      (a0 : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F)
      (g : GeneralLinear (t + 1) F),
      firstBlockFiberPoint F h q (lowerRadical h F Z0 * mixedEmbedding F h (a0, n) * g) =
        firstBlockFiberPoint F h (rightTranslate _ a0.val q) g := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (m 0 + 1)
  intro q Z0 a0 n g
  induction q using Quotient.inductionOn with
  | h v =>
    rw [rightTranslate_mk, firstBlockFiberPoint_mk, firstBlockFiberPoint_mk, ← mul_assoc,
      firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding, mul_assoc]
    exact TwoBlockUnipotentQuotient.mk_mul_of_mem _
      (lowerRadical_mul_leviEmbedding_one_mem F h _ n) _

variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  (μA : letI := borel (LeftUnipotentQuotient (m 0) F)
    Measure (LeftUnipotentQuotient (m 0) F))

/-- The inner slice integral of JPSS (4.9), (8): the total Bochner integral
`∫_{N_a \ GL_a^k} f(firstBlockFiberPoint q g) dμA(q)` over the published small slice, for
the supplied measure on the Borel structure of the small quotient. -/
def firstBlockFiberIntegral (k : ℤ) (f : LowerQuotient h F → ℂ)
    (g : GeneralLinear (t + 1) F) : ℂ :=
  letI := borel (LeftUnipotentQuotient (m 0) F)
  ∫ q in Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k,
    f (firstBlockFiberPoint F h q g) ∂μA

theorem firstBlockFiberIntegral_def (k : ℤ) (f : LowerQuotient h F → ℂ)
    (g : GeneralLinear (t + 1) F) :
    letI := borel (LeftUnipotentQuotient (m 0) F)
    firstBlockFiberIntegral F h μA k f g =
      ∫ q in Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k,
        f (firstBlockFiberPoint F h q g) ∂μA :=
  rfl

/-- Left invariance under `l = R(Z0) D(a0, n)`, without any integrability hypothesis: right
translation by `a0` preserves `μA` and, since `ord(det a0) = 0`, the small slice. -/
theorem firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul
    (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ) (f : LowerQuotient h F → ℂ)
    (Z0 : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (a0 : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F)
    (g : GeneralLinear (t + 1) F) :
    firstBlockFiberIntegral F h μA k f
        (lowerRadical h F Z0 * mixedEmbedding F h (a0, n) * g) =
      firstBlockFiberIntegral F h μA k f g := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let := borel (LeftUnipotentQuotient (m 0) F)
  let : BorelSpace (LeftUnipotentQuotient (m 0) F) := ⟨rfl⟩
  have hS : rightTranslate _ a0.val ⁻¹' Langlands.AllField.RankinSelberg.determinantSlice T (m 0) k =
      Langlands.AllField.RankinSelberg.determinantSlice T (m 0) k := by
    ext q
    rw [Set.mem_preimage, Langlands.AllField.RankinSelberg.rightTranslate_mem_determinantSlice T (m 0) k a0.val q,
      ord_determinant_eq_zero F a0.property, sub_zero]
  rw [firstBlockFiberIntegral_def, firstBlockFiberIntegral_def]
  simp_rw [firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul F h _ Z0 a0 n g]
  have hI := (hμA a0).setIntegral_preimage_emb (rightTranslate _ a0.val).measurableEmbedding
    (fun q => f (firstBlockFiberPoint F h q g)) (Langlands.AllField.RankinSelberg.determinantSlice T (m 0) k)
  rw [hS] at hI
  exact hI

/-- Left invariance under every element of the actual lower mixed subgroup. -/
theorem firstBlockFiberIntegral_lowerMixedSubgroup_mul
    (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ) (f : LowerQuotient h F → ℂ)
    (l : lowerMixedSubgroup F h) (g : GeneralLinear (t + 1) F) :
    firstBlockFiberIntegral F h μA k f (l.val * g) = firstBlockFiberIntegral F h μA k f g := by
  obtain ⟨Z0, a0, n, hl⟩ := lowerMixed_decomposition F h l.property
  rw [← hl]
  exact firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul F h μA hμA k f Z0 a0 n g

/-- The first-block slice average on the actual quotient `Lminus \ G`: the actual descent
of the left-`Lminus`-invariant inner slice integral. No coset representative is chosen. -/
def firstBlockAverage (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ)
    (f : LowerQuotient h F → ℂ) : LowerMixedQuotient F h → ℂ :=
  descend _ (firstBlockFiberIntegral F h μA k f)
    (firstBlockFiberIntegral_lowerMixedSubgroup_mul F h μA hμA k f)

/-- Representative evaluation of the first-block slice average. -/
theorem firstBlockAverage_mk (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ)
    (f : LowerQuotient h F → ℂ) (g : GeneralLinear (t + 1) F) :
    letI := borel (LeftUnipotentQuotient (m 0) F)
    firstBlockAverage F h μA hμA k f (Quotient.mk _ g) =
      ∫ q in Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k,
        f (firstBlockFiberPoint F h q g) ∂μA :=
  rfl

end FirstBlockFiber

end Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
