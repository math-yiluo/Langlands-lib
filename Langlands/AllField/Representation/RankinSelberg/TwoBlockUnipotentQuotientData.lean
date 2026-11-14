import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationCell
/-!
# The two-block unipotent quotient and its radical fiber average

JPSS (1983), Section 4.6, printed pages 411-412: the first unfolding passes from
equation (4), an iterated integral over `N_r \ G_r^m` and the complementary upper
radical, to the integral over `N_(t_1,t_2) \ G_r^m`, where `N_(t_1,t_2)` is the group
(5) of block diagonal matrices `diag(n_1, n_2)` with `n_i` upper unipotent.

For two blocks of sizes `m 0 + 1` and `m 1 + 1` of total rank `t + 1`, this module
constructs that subgroup `H` of `GL_(t+1)`, the actual left quotient `H \ GL_(t+1)`
with the projection to `N \ GL_(t+1)`, the radical fiber map
`(x, g) ↦ [u(x) g]_H`, its unweighted fiber integral, the descended radical average on
`N \ GL_(t+1)` and the determinant slices of `H \ GL_(t+1)`. No integrability,
quotient-measure, or Fubini statement is asserted.
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice radicalAverage radicalAverage_mk
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding determinantSlice iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice

open Langlands.GeneralLinear hiding blockUnipotent
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent inducedRep_mem_compactRadicalSubmodule integral_comp_unipotentShift inverseStandardCharacter_eq_prod isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.QuotientIntegration

universe uF uR uG

section Algebra

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]

/-! ### The block-diagonal upper-unipotent subgroup -/

end Algebra

/-! ### Topology of the subgroup -/

section Topology

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]
variable [TopologicalSpace R]

section Ring


end Ring


end Topology

section Canonical


end Canonical

/-! ### The intermediate quotient and the radical fiber map -/

section Quotient


end Quotient

section Padic

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The projection `H \ G → N \ G` is continuous for the quotient topologies. -/
theorem continuous_projection [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Continuous (projection h F) := by
  exact Continuous.quotient_lift continuous_quotient_mk' _

/-- The radical fiber map is jointly continuous in `(x, g)`. -/
theorem continuous_fiberPoint [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Continuous (Function.uncurry (fiberPoint h F)) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (t + 1)
  exact continuous_quotient_mk'.comp
    (((continuous_upperRadical h F).comp continuous_fst).mul continuous_snd)

/-! ### The radical fiber integral and its descent -/

section Average

variable [MeasurableSpace F]

/-- The unweighted radical fiber integral `g ↦ ∫ f([u(x) g]_H) dμ(x)`, the ordinary total
Bochner integral against the supplied measure on the rectangle. -/
def fiberIntegral (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
    (f : BlockQuotient h F → ℂ) (g : GeneralLinear (t + 1) F) : ℂ :=
  ∫ x, f (fiberPoint h F x g) ∂μ

theorem fiberIntegral_def [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
    (f : BlockQuotient h F → ℂ) (g : GeneralLinear (t + 1) F) :
    fiberIntegral F h μ f g = ∫ x, f (fiberPoint h F x g) ∂μ :=
  rfl

/-- Left `N`-invariance of the fiber integral, for every Borel additive Haar measure on the
rectangle and every scalar function, without any integrability hypothesis. -/
theorem fiberIntegral_upperUnipotent_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ [BorelSpace F]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μ.IsAddHaarMeasure]
      (f : BlockQuotient h F → ℂ) (n : upperUnipotent (t + 1) F)
      (g : GeneralLinear (t + 1) F),
      fiberIntegral F h μ f (n.val * g) = fiberIntegral F h μ f g := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ μ _ f n g
  have : SecondCountableTopology F := T.secondCountableTopology
  simp only [fiberIntegral_def, fiberPoint_upperUnipotent_mul]
  exact integral_comp_unipotentShift F h μ n (fun y => f (fiberPoint h F y g))

/-- The radical average on the actual quotient `N \ GL_(t+1)`: the actual descent of the
left-`N`-invariant fiber integral. No coset representative is chosen. -/
def radicalAverage [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ [BorelSpace F]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μ.IsAddHaarMeasure],
      (BlockQuotient h F → ℂ) → LeftUnipotentQuotient t F → ℂ := by
  intro _ μ _ f
  exact descend _ (fiberIntegral F h μ f)
    (fun n g => fiberIntegral_upperUnipotent_mul F h μ f n g)

/-- Representative evaluation of the radical average. -/
theorem radicalAverage_mk [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ [BorelSpace F]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μ.IsAddHaarMeasure]
      (f : BlockQuotient h F → ℂ) (g : GeneralLinear (t + 1) F),
      radicalAverage F h μ f (Quotient.mk _ g) = ∫ x, f (fiberPoint h F x g) ∂μ := by
  intro _ μ _ f g
  rfl

end Average

/-! ### Determinant slices -/

/-- The determinant slice of `H \ GL_(t+1)`: the preimage under `projection` of the published
slice `N \ G^k = {ord(det g) = k}`. -/
def determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) : Set (BlockQuotient h F) :=
  projection h F ⁻¹' Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t k

/-- Representative condition `ord(det g) = k`, for the published normalized order. -/
theorem mk_mem_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {k : ℤ} {g : GeneralLinear (t + 1) F} :
    (Quotient.mk _ g : BlockQuotient h F) ∈ determinantSlice F h k ↔
      (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) = k :=
  Iff.rfl

theorem isClopen_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) :
    IsClopen (determinantSlice F h k) := by
  exact (Langlands.AllField.RankinSelberg.isClopen_determinantSlice (⟨⟩ : LocalFieldData F) t k).preimage
    (continuous_projection F h)

/-- Every slice is measurable for any Borel structure on the intermediate quotient. -/
theorem measurableSet_determinantSlice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (k : ℤ) :
    ∀ [MeasurableSpace (BlockQuotient h F)] [BorelSpace (BlockQuotient h F)],
      MeasurableSet (determinantSlice F h k) := by
  intro _ _
  exact (isClopen_determinantSlice F h k).isOpen.measurableSet

end Padic

end Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
