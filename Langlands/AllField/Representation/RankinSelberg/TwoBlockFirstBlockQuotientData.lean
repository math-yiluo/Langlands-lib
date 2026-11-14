import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData
import Langlands.AllField.Representation.Jacquet.ParabolicSupplement
import Langlands.AllField.Representation.Parabolic.FlattenedRefinementModulusCalculation
import Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
/-!
# The first-block norm-one quotient and the first-block slice average

JPSS (1983), Section 4.6, printed page 412, equation (6): for `r = t_1 + t_2`,

`∫_{N_(t_1,t_2) \ G_r^m} f(g) dg =
  ∫_{G_(t_1)^0 N_(t_1,t_2) \ G_r^0} dh ∫_{N_(t_1) \ G_(t_1)^m} f[diag(a, 1) h] d^×a`.

For two blocks of sizes `a = m 0 + 1` and `b = m 1 + 1` of total rank `t + 1`, this module
constructs the actual data of this displayed formula: the first-block embedding
`u ↦ diag(u, 1_b)`, the subgroup `L = diag(GL_a^0, N_b) = G_(t_1)^0 N_(t_1,t_2)` with its
quotient `L \ GL_(t+1)` and determinant slices, the fiber map
`([u], g) ↦ [diag(u, 1) g]_H` from the small quotient `N_a \ GL_a` to
`H \ GL_(t+1)` with `H = N_(t_1,t_2)`, the inner slice integral and its descent to
`L \ GL_(t+1)`. No integrability, quotient-measure, or Fubini statement is asserted.
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice isClosed_mixedSubgroup measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice rightTranslate_mem_determinantSlice

open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent inducedRep_mem_compactRadicalSubmodule integral_comp_unipotentShift inverseStandardCharacter_eq_prod isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.QuotientIntegration

universe uF uR

/-! ### Block-diagonal matrices -/

section Algebra



end Algebra

section TwoBlocks

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]

/-! ### The first-block embedding -/

/-! ### Matrices with vanishing off-diagonal blocks -/

end TwoBlocks

section AlgebraTopology


end AlgebraTopology

/-! ### The last row and the fiber map -/

section Field


end Field

/-! ### The norm-one first block and the mixed subgroup -/

section Padic

variable (F : Type uF) [Field F]

/-- The norm-one subgroup `GL_n^0 = {u | |det u| = 1}`, the kernel of the published
determinant norm for the canonical realization. -/
abbrev normOneSubgroup [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n : ℕ) : Subgroup (GeneralLinear n F) :=
  ((⟨⟩ : LocalFieldData F).determinantNorm n).ker

theorem mem_normOneSubgroup_iff [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {n : ℕ} (u : GeneralLinear n F) :
    u ∈ normOneSubgroup F n ↔ (⟨⟩ : LocalFieldData F).determinantNorm n u = 1 :=
  Iff.rfl

/-- Norm one is the condition `|det u| = 1` for the normalized absolute value. -/
theorem mem_normOneSubgroup_iff_normalizedAbs [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {n : ℕ} (u : GeneralLinear n F) :
    u ∈ normOneSubgroup F n ↔
      (⟨⟩ : LocalFieldData F).normalizedAbs (u : Matrix (Fin n) (Fin n) F).det = 1 := by
  rw [MonoidHom.mem_ker, ← Units.val_inj, ← NNReal.coe_inj,
    Langlands.LocalFieldData.determinantNorm_coe, Units.val_one, NNReal.coe_one,
    Matrix.GeneralLinearGroup.val_det_apply]

/-- A norm-one matrix has determinant of order zero. -/
theorem ord_determinant_eq_zero [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {n : ℕ} {u : GeneralLinear n F}
    (hu : u ∈ normOneSubgroup F n) :
    (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant u : F) = 0 := by
  rw [Langlands.LocalFieldData.ord_eq_zero_iff_normalizedAbs,
    Matrix.GeneralLinearGroup.val_det_apply]
  exact (mem_normOneSubgroup_iff_normalizedAbs F u).mp hu

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The embedding `(u, n) ↦ diag(u, n)` of `GL_(m 0 + 1)^0 × N_(m 1 + 1)` into
`GL_(t+1)`, through the published Levi embedding of `succBlockShape m h`. -/
def mixedEmbedding [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F →*
      GeneralLinear (t + 1) F :=
  ((succBlockShape m h).leviEmbedding F).comp ((blockPair F).comp
    (MonoidHom.prodMap (normOneSubgroup F (m 0 + 1)).subtype
      (upperUnipotent (m 1 + 1) F).subtype))

theorem mixedEmbedding_apply [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F) :
    mixedEmbedding F h x =
      (succBlockShape m h).leviEmbedding F (blockPair F (x.1.val, x.2.val)) :=
  rfl

@[simp]
theorem mixedEmbedding_index_zero_zero [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F)
    (a b : Fin (m 0 + 1)) :
    mixedEmbedding F h x ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 0 b) =
      x.1.val a b := by
  rw [mixedEmbedding_apply, BlockShape.leviEmbedding_apply_same]
  simp

@[simp]
theorem mixedEmbedding_index_zero_one [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F)
    (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)) :
    mixedEmbedding F h x ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) =
      0 :=
  leviEmbedding_index_zero_one h _ a b

@[simp]
theorem mixedEmbedding_index_one_zero [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F)
    (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)) :
    mixedEmbedding F h x ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) =
      0 :=
  leviEmbedding_index_one_zero h _ a b

@[simp]
theorem mixedEmbedding_index_one_one [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F)
    (a b : Fin (m 1 + 1)) :
    mixedEmbedding F h x ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 b) =
      x.2.val a b := by
  rw [mixedEmbedding_apply, BlockShape.leviEmbedding_apply_same]
  simp

/-- `det diag(u, n) = det u`. -/
@[simp]
theorem determinant_mixedEmbedding [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F) :
    GeneralLinear.determinant (mixedEmbedding F h x) = GeneralLinear.determinant x.1.val := by
  rw [mixedEmbedding_apply, determinant_leviEmbedding_blockPair,
    TwoBlockUnipotentQuotient.determinant_eq_one_of_mem_upperUnipotent F x.2.property,
    mul_one]

/-- The subgroup `L = G_(t_1)^0 N_(t_1,t_2) = diag(GL_(m 0 + 1)^0, N_(m 1 + 1))` of JPSS
(4.6), (6): the actual image of `mixedEmbedding`. -/
def mixedSubgroup [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : Subgroup (GeneralLinear (t + 1) F) :=
  (mixedEmbedding F h).range

theorem mixedEmbedding_mem [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F) :
    mixedEmbedding F h x ∈ mixedSubgroup F h :=
  ⟨x, rfl⟩

/-- Intrinsic block-entry description of `L`: both off-diagonal blocks vanish, the first
diagonal block has determinant of normalized absolute value one (so it is invertible), and
the second diagonal block is upper unipotent. -/
theorem mem_mixedSubgroup_iff [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (t + 1) F) :
    g ∈ mixedSubgroup F h ↔
      (∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
        g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0) ∧
      (∀ (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)),
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0) ∧
      (⟨⟩ : LocalFieldData F).normalizedAbs
        ((g : Matrix (Fin (t + 1)) (Fin (t + 1)) F).submatrix
          ((succBlockShape m h).index 0) ((succBlockShape m h).index 0)).det = 1 ∧
      (∀ (a b : Fin (m 1 + 1)), b < a →
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 b) = 0) ∧
      (∀ a : Fin (m 1 + 1),
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 a) = 1) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨mixedEmbedding_index_zero_one F h x, mixedEmbedding_index_one_zero F h x, ?_,
      fun a b hab => ?_, fun a => ?_⟩
    · have hsub : ((mixedEmbedding F h x : Matrix (Fin (t + 1)) (Fin (t + 1)) F).submatrix
          ((succBlockShape m h).index 0) ((succBlockShape m h).index 0)) =
          (x.1.val : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F) := by
        ext a b
        exact mixedEmbedding_index_zero_zero F h x a b
      rw [hsub]
      exact (mem_normOneSubgroup_iff_normalizedAbs F x.1.val).mp x.1.property
    · rw [mixedEmbedding_index_one_one]
      exact UpperUnipotent.entry_eq_zero x.2 hab
    · rw [mixedEmbedding_index_one_one]
      exact UpperUnipotent.entry_diag x.2 a
  · rintro ⟨h01, h10, hdet, hlow, hdiag⟩
    have hg := mem_parabolic_of_index_one_zero h F g h10
    set L := (succBlockShape m h).leviProjection F ⟨g, hg⟩ with hLdef
    have hL0 : L 0 ∈ normOneSubgroup F (m 0 + 1) := by
      rw [mem_normOneSubgroup_iff_normalizedAbs]
      exact hdet
    have hL1 : L 1 ∈ upperUnipotent (m 1 + 1) F :=
      ⟨fun a b hab => hlow a b hab, hdiag⟩
    refine ⟨(⟨L 0, hL0⟩, ⟨L 1, hL1⟩), ?_⟩
    change (succBlockShape m h).leviEmbedding F (blockPair F (L 0, L 1)) = g
    rw [blockPair_eta]
    exact leviEmbedding_leviProjection_of_blocks h F g hg h01 h10

/-- Equivalent intrinsic description with the determinant norm of the whole matrix: this
form exhibits `L` as an intersection of closed conditions. -/
theorem mem_mixedSubgroup_iff_determinantNorm [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (t + 1) F) :
    g ∈ mixedSubgroup F h ↔
      (∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
        g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0) ∧
      (∀ (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)),
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0) ∧
      g ∈ normOneSubgroup F (t + 1) ∧
      (∀ (a b : Fin (m 1 + 1)), b < a →
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 b) = 0) ∧
      (∀ a : Fin (m 1 + 1),
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 a) = 1) := by
  rw [mem_mixedSubgroup_iff]
  constructor
  · rintro ⟨h01, h10, hdet, hlow, hdiag⟩
    refine ⟨h01, h10, ?_, hlow, hdiag⟩
    rw [mem_normOneSubgroup_iff_normalizedAbs, ← Matrix.GeneralLinearGroup.val_det_apply,
      ← det_firstBlock_eq h F g h01 h10 hlow hdiag]
    exact hdet
  · rintro ⟨h01, h10, hdet, hlow, hdiag⟩
    refine ⟨h01, h10, ?_, hlow, hdiag⟩
    rw [det_firstBlock_eq h F g h01 h10 hlow hdiag,
      Matrix.GeneralLinearGroup.val_det_apply]
    exact (mem_normOneSubgroup_iff_normalizedAbs F g).mp hdet

/-- `L ≤ ker |det|`. -/
theorem mixedSubgroup_le_normOneSubgroup [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : mixedSubgroup F h ≤ normOneSubgroup F (t + 1) := by
  rintro _ ⟨x, rfl⟩
  change (⟨⟩ : LocalFieldData F).normalizedAbsUnits
    (GeneralLinear.determinant (mixedEmbedding F h x)) = 1
  rw [determinant_mixedEmbedding]
  exact x.1.property

/-- `H = N_(t_1,t_2) ≤ L`: the first block of `H` is upper unipotent, hence of norm one. -/
theorem blockUnipotent_le_mixedSubgroup [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    TwoBlockUnipotentQuotient.blockUnipotent h F ≤ mixedSubgroup F h := by
  rintro _ ⟨n, rfl⟩
  refine ⟨(⟨(n 0).val, determinantNorm_eq_one_of_mem_upperUnipotent F
    (⟨⟩ : LocalFieldData F) (n 0).property⟩, n 1), ?_⟩
  rw [mixedEmbedding_apply, TwoBlockUnipotentQuotient.blockEmbedding_apply]
  exact congrArg _ (blockPair_eta F fun i => (n i).val)

theorem mixedSubgroup_le_parabolic [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    mixedSubgroup F h ≤ (succBlockShape m h).parabolic F := fun g hg =>
  mem_parabolic_of_index_one_zero h F g ((mem_mixedSubgroup_iff F h g).mp hg).2.1

/-- The diagonal blocks of an element of `L`, by the published Levi projection. -/
def mixedCoordinates [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : mixedSubgroup F h) :
    normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F :=
  (⟨(succBlockShape m h).leviProjection F
      ⟨g.val, mixedSubgroup_le_parabolic F h g.property⟩ 0, by
      rw [mem_normOneSubgroup_iff_normalizedAbs]
      exact ((mem_mixedSubgroup_iff F h g.val).mp g.property).2.2.1⟩,
    ⟨(succBlockShape m h).leviProjection F
      ⟨g.val, mixedSubgroup_le_parabolic F h g.property⟩ 1,
      ⟨fun a b hab => ((mem_mixedSubgroup_iff F h g.val).mp g.property).2.2.2.1 a b hab,
        ((mem_mixedSubgroup_iff F h g.val).mp g.property).2.2.2.2⟩⟩)

theorem mixedCoordinates_mixedEmbedding [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F) :
    mixedCoordinates F h ⟨mixedEmbedding F h x, mixedEmbedding_mem F h x⟩ = x := by
  refine Prod.ext (Subtype.ext (Matrix.GeneralLinearGroup.ext fun a b => ?_))
    (Subtype.ext (Matrix.GeneralLinearGroup.ext fun a b => ?_))
  · change (succBlockShape m h).leviProjection F
      ⟨mixedEmbedding F h x, mixedSubgroup_le_parabolic F h (mixedEmbedding_mem F h x)⟩ 0 a b = _
    rw [BlockShape.leviProjection_apply]
    exact mixedEmbedding_index_zero_zero F h x a b
  · change (succBlockShape m h).leviProjection F
      ⟨mixedEmbedding F h x, mixedSubgroup_le_parabolic F h (mixedEmbedding_mem F h x)⟩ 1 a b = _
    rw [BlockShape.leviProjection_apply]
    exact mixedEmbedding_index_one_one F h x a b

theorem mixedEmbedding_mixedCoordinates [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : mixedSubgroup F h) :
    mixedEmbedding F h (mixedCoordinates F h g) = g.val := by
  rw [mixedEmbedding_apply]
  change (succBlockShape m h).leviEmbedding F
    (blockPair F (((succBlockShape m h).leviProjection F
      ⟨g.val, mixedSubgroup_le_parabolic F h g.property⟩ 0),
      ((succBlockShape m h).leviProjection F
      ⟨g.val, mixedSubgroup_le_parabolic F h g.property⟩ 1))) = g.val
  rw [blockPair_eta]
  exact leviEmbedding_leviProjection_of_blocks h F g.val _
    ((mem_mixedSubgroup_iff F h g.val).mp g.property).1
    ((mem_mixedSubgroup_iff F h g.val).mp g.property).2.1

/-- The multiplicative equivalence of `GL_(m 0 + 1)^0 × N_(m 1 + 1)` with `L`; the inverse
extracts the diagonal blocks. -/
def mixedSubgroupEquiv [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F ≃* mixedSubgroup F h where
  toFun x := ⟨mixedEmbedding F h x, mixedEmbedding_mem F h x⟩
  invFun := mixedCoordinates F h
  left_inv := mixedCoordinates_mixedEmbedding F h
  right_inv g := Subtype.ext (mixedEmbedding_mixedCoordinates F h g)
  map_mul' x y := Subtype.ext (map_mul (mixedEmbedding F h) x y)

@[simp]
theorem mixedSubgroupEquiv_apply_val [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F) :
    (mixedSubgroupEquiv F h x).val = mixedEmbedding F h x :=
  rfl

/-- The equivalence `GL_(m 0 + 1)^0 × N_(m 1 + 1) ≃ L` is a homeomorphism for the canonical
p-adic topology. -/
def mixedSubgroupHomeomorph [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F ≃ₜ* mixedSubgroup F h :=
  { toMulEquiv := mixedSubgroupEquiv F h
    continuous_toFun :=
      (((succBlockShape m h).leviEmbeddingContinuous F).continuous.comp
        ((continuous_blockPair F).comp
          ((continuous_subtype_val.comp continuous_fst).prodMk
            (continuous_subtype_val.comp continuous_snd)))).subtype_mk _
    continuous_invFun := by
      have hP : Continuous (fun g : mixedSubgroup F h =>
          (succBlockShape m h).leviProjection F
            ⟨g.val, mixedSubgroup_le_parabolic F h g.property⟩) :=
        ((succBlockShape m h).leviProjectionContinuous F).continuous.comp
          (continuous_subtype_val.subtype_mk _)
      exact (((continuous_apply 0).comp hP).subtype_mk _).prodMk
        (((continuous_apply 1).comp hP).subtype_mk _) }

/-- `L` is closed: it is cut out by the vanishing of the off-diagonal blocks, the
upper-unipotent conditions on the second block, and the open, hence closed, kernel of
`|det|`. -/
theorem isClosed_mixedSubgroup [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    IsClosed (mixedSubgroup F h : Set (GeneralLinear (t + 1) F)) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (t + 1)
  have he : (mixedSubgroup F h : Set (GeneralLinear (t + 1) F)) =
      (⋂ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)), {g : GeneralLinear (t + 1) F |
        g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0}) ∩
      ((⋂ (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)), {g : GeneralLinear (t + 1) F |
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0}) ∩
      ((normOneSubgroup F (t + 1) : Set (GeneralLinear (t + 1) F)) ∩
      ((⋂ (a : Fin (m 1 + 1)) (b : Fin (m 1 + 1)) (_ : b < a),
        {g : GeneralLinear (t + 1) F |
          g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 b) = 0}) ∩
      (⋂ (a : Fin (m 1 + 1)), {g : GeneralLinear (t + 1) F |
        g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 a) = 1})))) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_mixedSubgroup_iff_determinantNorm F h g
  have hentry : ∀ (k l : Fin (t + 1)) (c : F),
      IsClosed {g : GeneralLinear (t + 1) F | g k l = c} := fun k l c =>
    isClosed_eq (GeneralLinear.entry (R := F) k l).continuous continuous_const
  rw [he]
  exact (isClosed_iInter fun a => isClosed_iInter fun b => hentry _ _ _).inter
    ((isClosed_iInter fun a => isClosed_iInter fun b => hentry _ _ _).inter
      ((Subgroup.isClosed_of_isOpen _ (T.isOpen_ker_determinantNorm (t + 1))).inter
        ((isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
          hentry _ _ _).inter
          (isClosed_iInter fun a => hentry _ _ _))))

/-! ### The mixed quotient `L \ GL_(t+1)` -/

/-- The actual left quotient `L \ GL_(t+1)`. -/
abbrev MixedQuotient [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] := LeftQuotient (mixedSubgroup F h)

/-- The quotient determinant order `[g]_L ↦ ord(det g)`; it is well defined because every
element of `L` has determinant of order zero. -/
def determinantOrder [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : MixedQuotient F h → ℤ :=
  descend _
    (fun g => (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F))
    (fun l g => by
      rw [map_mul, Units.val_mul,
        (⟨⟩ : LocalFieldData F).ord_mul (GeneralLinear.determinant l.val).ne_zero
          (GeneralLinear.determinant g).ne_zero,
        ord_determinant_eq_zero F (mixedSubgroup_le_normOneSubgroup F h l.property), zero_add])

@[simp]
theorem determinantOrder_mk [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (t + 1) F) :
    determinantOrder F h (Quotient.mk _ g) =
      (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) :=
  rfl

/-- The determinant order is continuous into the discrete integers. -/
theorem continuous_determinantOrder [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Continuous (determinantOrder F h) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  exact Continuous.quotient_lift
    ((continuous_ord_units T).comp (T.generalLinearDeterminant (t + 1)).continuous) _

/-- The determinant slice `L \ G^k = {q | ord(det q) = k}` of the mixed quotient. The
outer domain of JPSS (4.6), (6) is the slice `k = 0`. -/
def determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) : Set (MixedQuotient F h) :=
  {q | determinantOrder F h q = k}

theorem mem_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {k : ℤ} {q : MixedQuotient F h} :
    q ∈ determinantSlice F h k ↔ determinantOrder F h q = k :=
  Iff.rfl

theorem isClopen_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) :
    IsClopen (determinantSlice F h k) := by
  exact (isClopen_discrete ({k} : Set ℤ)).preimage (continuous_determinantOrder F h)

/-- Every slice is measurable for any Borel structure on the mixed quotient. -/
theorem measurableSet_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) :
    ∀ [MeasurableSpace (MixedQuotient F h)] [BorelSpace (MixedQuotient F h)],
      MeasurableSet (determinantSlice F h k) := by
  intro _ _
  exact (isClopen_determinantSlice F h k).isOpen.measurableSet

/-! ### The fiber map from the small quotient -/

/-- The fiber map is jointly continuous in `(q, g)`. -/
theorem continuous_fiberPoint [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Continuous (Function.uncurry (fiberPoint h F)) := by
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
  have he : Function.uncurry (fiberPoint h F) ∘
      Prod.map (leftQuotientMap (upperUnipotent (m 0 + 1) F)) id =
      fun x : GeneralLinear (m 0 + 1) F × GeneralLinear (t + 1) F =>
        (Quotient.mk _ (firstBlockEmbedding h F x.1 * x.2) :
          TwoBlockUnipotentQuotient.BlockQuotient h F) :=
    rfl
  rw [he]
  exact continuous_quotient_mk'.comp
    (((continuous_firstBlockEmbedding h F).comp continuous_fst).mul continuous_snd)

/-- `fiberPoint q g` lies in the published slice `H \ G^k` exactly when
`ord(det q) + ord(det g) = k`. -/
theorem fiberPoint_mem_determinantSlice_iff [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (q : LeftUnipotentQuotient (m 0) F)
    (g : GeneralLinear (t + 1) F) (k : ℤ) :
    fiberPoint h F q g ∈ Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h k ↔
      Langlands.AllField.RankinSelberg.determinantOrder (⟨⟩ : LocalFieldData F) (m 0) q +
        (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) = k := by
  induction q using Quotient.inductionOn with
  | h u =>
    rw [fiberPoint_mk, Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.mk_mem_determinantSlice,
      Langlands.AllField.RankinSelberg.determinantOrder_mk, map_mul, Units.val_mul,
      (⟨⟩ : LocalFieldData F).ord_mul
        (GeneralLinear.determinant (firstBlockEmbedding h F u)).ne_zero
        (GeneralLinear.determinant g).ne_zero,
      determinant_firstBlockEmbedding]

/-- Change of fiber: left multiplication of the base point by `diag(u, n) ∈ L` is right
multiplication of the small quotient by `u`. -/
theorem fiberPoint_mixedEmbedding_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (m 0 + 1)
    ∀ (q : LeftUnipotentQuotient (m 0) F) (u : normOneSubgroup F (m 0 + 1))
      (n : upperUnipotent (m 1 + 1) F) (g : GeneralLinear (t + 1) F),
      fiberPoint h F q (mixedEmbedding F h (u, n) * g) =
        fiberPoint h F (rightTranslate _ u.val q) g := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (m 0 + 1)
  intro q u n g
  induction q using Quotient.inductionOn with
  | h v =>
    rw [rightTranslate_mk, fiberPoint_mk, fiberPoint_mk, ← mul_assoc, mixedEmbedding_apply,
      firstBlockEmbedding_mul_leviEmbedding_blockPair, mul_assoc]
    exact TwoBlockUnipotentQuotient.mk_mul_of_mem _
      (leviEmbedding_blockPair_mem_blockUnipotent h F
        (upperUnipotent (m 0 + 1) F).one_mem n.property) _

/-! ### The inner slice integral and the first-block average -/

/-- Right translation of the small quotient by every norm-one `u` preserves the measure,
for the Borel structure of the quotient topology. -/
def NormOneRightInvariant [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n : ℕ)
    (μA : letI := borel (LeftUnipotentQuotient n F)
      Measure (LeftUnipotentQuotient n F)) : Prop :=
  letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (n + 1)
  letI := borel (LeftUnipotentQuotient n F)
  ∀ u : normOneSubgroup F (n + 1), MeasurePreserving (rightTranslate _ u.val) μA μA

/-- A compatible quotient measure on the small full-unipotent quotient, in the sense of the
published `QuotientIntegration.IsCompatible`, is invariant under all right translations,
in particular under those by norm-one matrices. -/
theorem normOneRightInvariant_of_isCompatible [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n : ℕ) :
    letI := borel (LeftUnipotentQuotient n F)
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ [MeasurableSpace (GeneralLinear (n + 1) F)]
      [BorelSpace (GeneralLinear (n + 1) F)]
      [MeasurableSpace (upperUnipotent (n + 1) F)]
      [BorelSpace (upperUnipotent (n + 1) F)]
      [MeasurableMul (upperUnipotent (n + 1) F)]
      (μG : Measure (GeneralLinear (n + 1) F))
      (μH : Measure (upperUnipotent (n + 1) F)) [Measure.IsMulRightInvariant μH]
      (ν : Measure (LeftUnipotentQuotient n F)),
      IsCompatible (upperUnipotent (n + 1) F) μG μH ν → NormOneRightInvariant F n ν := by
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro _ _ _ _ _ μG μH _ ν hν u
  exact hν.right_invariant u.val

variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  (μA : letI := borel (LeftUnipotentQuotient (m 0) F)
    Measure (LeftUnipotentQuotient (m 0) F))

/-- The inner integral of JPSS (4.6), (6): the total Bochner integral
`∫_{N_a \ GL_a^k} f(fiberPoint q g) dμA(q)` over the published small slice, for the supplied
measure on the Borel structure of the small quotient. -/
def fiberIntegral (k : ℤ) (f : TwoBlockUnipotentQuotient.BlockQuotient h F → ℂ)
    (g : GeneralLinear (t + 1) F) : ℂ :=
  letI := borel (LeftUnipotentQuotient (m 0) F)
  ∫ q in Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k,
    f (fiberPoint h F q g) ∂μA

theorem fiberIntegral_def (k : ℤ) (f : TwoBlockUnipotentQuotient.BlockQuotient h F → ℂ)
    (g : GeneralLinear (t + 1) F) :
    letI := borel (LeftUnipotentQuotient (m 0) F)
    fiberIntegral F h μA k f g =
      ∫ q in Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k,
        f (fiberPoint h F q g) ∂μA :=
  rfl

/-- Left invariance under `diag(u, n) ∈ L`, without any integrability hypothesis: right
translation by `u` preserves `μA` and, since `ord(det u) = 0`, the small slice. -/
theorem fiberIntegral_mixedEmbedding_mul (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ)
    (f : TwoBlockUnipotentQuotient.BlockQuotient h F → ℂ)
    (u : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F)
    (g : GeneralLinear (t + 1) F) :
    fiberIntegral F h μA k f (mixedEmbedding F h (u, n) * g) = fiberIntegral F h μA k f g := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let := borel (LeftUnipotentQuotient (m 0) F)
  let : BorelSpace (LeftUnipotentQuotient (m 0) F) := ⟨rfl⟩
  have hS : rightTranslate _ u.val ⁻¹' Langlands.AllField.RankinSelberg.determinantSlice T (m 0) k =
      Langlands.AllField.RankinSelberg.determinantSlice T (m 0) k := by
    ext q
    rw [Set.mem_preimage, Langlands.AllField.RankinSelberg.rightTranslate_mem_determinantSlice T (m 0) k u.val q,
      ord_determinant_eq_zero F u.property, sub_zero]
  rw [fiberIntegral_def, fiberIntegral_def]
  simp_rw [fiberPoint_mixedEmbedding_mul F h _ u n g]
  have hI := (hμA u).setIntegral_preimage_emb (rightTranslate _ u.val).measurableEmbedding
    (fun q => f (fiberPoint h F q g)) (Langlands.AllField.RankinSelberg.determinantSlice T (m 0) k)
  rw [hS] at hI
  exact hI

/-- Left invariance under every element of `L`. -/
theorem fiberIntegral_mixedSubgroup_mul (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ)
    (f : TwoBlockUnipotentQuotient.BlockQuotient h F → ℂ) (l : mixedSubgroup F h)
    (g : GeneralLinear (t + 1) F) :
    fiberIntegral F h μA k f (l.val * g) = fiberIntegral F h μA k f g := by
  obtain ⟨x, hx⟩ := l.property
  rw [← hx]
  exact fiberIntegral_mixedEmbedding_mul F h μA hμA k f x.1 x.2 g

/-- The first-block average on the actual quotient `L \ GL_(t+1)`: the actual descent of
the left-`L`-invariant inner slice integral. No coset representative is chosen. -/
def firstBlockAverage (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ)
    (f : TwoBlockUnipotentQuotient.BlockQuotient h F → ℂ) : MixedQuotient F h → ℂ :=
  descend _ (fiberIntegral F h μA k f) (fiberIntegral_mixedSubgroup_mul F h μA hμA k f)

/-- Representative evaluation of the first-block average. -/
theorem firstBlockAverage_mk (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ)
    (f : TwoBlockUnipotentQuotient.BlockQuotient h F → ℂ)
    (g : GeneralLinear (t + 1) F) :
    letI := borel (LeftUnipotentQuotient (m 0) F)
    firstBlockAverage F h μA hμA k f (Quotient.mk _ g) =
      ∫ q in Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k,
        f (fiberPoint h F q g) ∂μA :=
  rfl

end Padic

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
