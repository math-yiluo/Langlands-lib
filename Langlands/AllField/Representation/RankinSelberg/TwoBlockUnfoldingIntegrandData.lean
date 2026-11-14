import Langlands.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
/-!
# The integrand of the first Section 4.6 unfolding

JPSS (1983), Section 4.6, equation (4) on printed page 411 and the first integral on
printed page 412: after substituting the Jacquet integral (4.6.2) into the outer integral
over `N_r \ G_r^m`, the iterated integrand is unfolded to the integral of
`W(g) f[g; e, e] Φ(η g)` over `N_(t_1,t_2) \ G_r^m`, where `N_(t_1,t_2)` is the
block-diagonal upper-unipotent group (5).

For two blocks of sizes `m 0 + 1` and `m 1 + 1` of total rank `t + 1`, actual block
functionals `ℓ_i` in the inverse-character spaces, a lower normalized section `f`, a test
function `W` in the standard-character space and a Schwartz–Bruhat function `Φ`, this
module constructs the scalar function

`[g]_H ↦ W(g) ⟨f(g), ⊗ ℓ_i⟩ Φ(lastRow g)`

on the published quotient `H \ GL_(t+1)`, `H = blockUnipotent h F`, by actual
quotient descent. It proves the block covariance of the scalar section, the left
`H`-invariance, the representative formula, the fiber formula through the positive
Jacquet kernel, and the identities of the total fiber integral and the radical average
with `W(g) J(f)(g) Φ(lastRow g)`. No integrability, measurability or Fubini statement is
asserted.
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.RankinSelberg.TwoBlockUnfolding
open Langlands.RankinSelberg.TwoBlockUnfolding hiding fiberIntegral_integrand groupIntegrand groupIntegrand_blockUnipotent_mul groupIntegrand_def integrand integrand_fiberPoint integrand_mk inverseStandardCharacter_blockEmbedding radicalAverage_integrand_mk scalarSection_blockEmbedding_mul scalarSection_blockEmbedding_mul_eq_inverseStandardCharacter
open Langlands.AllField.RankinSelberg.TwoBlockUnfolding
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet hiding integrand
open Langlands.RankinSelberg.TwoBlockDeformation hiding compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent inducedRep_mem_compactRadicalSubmodule integral_comp_unipotentShift inverseStandardCharacter_eq_prod isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice radicalAverage radicalAverage_mk
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient hiding determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.QuotientIntegration
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uW

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F}

/-! ### Block covariance of the scalar section -/

section Covariance

variable (ell : ∀ i, Whittaker.glInverseFunctionals ψ (m i) (σ i))

/-- Left translation by `diag(n_0, n_1)` multiplies the scalar section at the Levi identity
by the product of the two block inverse standard characters `ψ⁻¹(n_0) ψ⁻¹(n_1)`. -/
theorem scalarSection_blockEmbedding_mul (f : Sections F h σ) (n : BlockUnipotents m F)
    (g : GeneralLinear (t + 1) F) :
    scalarSection (fun i => (ell i).val) f (blockEmbedding h F n * g) 1 =
      (∏ i, (inverseStandardCharacter ψ (m i) (n i) : ℂ)) *
        scalarSection (fun i => (ell i).val) f g 1 := by
  rw [scalarSection_one, scalarSection_one, blockEmbedding_apply,
    sectionEval_leviEmbedding_mul F h σ f _
      (fun i => determinantNorm_eq_one_of_mem_upperUnipotent F _ (n i).property) g,
    tensorContraction_blockTensor F h σ ψ _ (fun i => (ell i).property) _
      (fun i => (n i).property)]

/-- The product of the two block inverse standard characters of `(n_0, n_1)` is the
ambient inverse standard character of `diag(n_0, n_1)`: the corner block vanishes. -/
theorem inverseStandardCharacter_blockEmbedding (n : BlockUnipotents m F) :
    (inverseStandardCharacter ψ t
        ⟨blockEmbedding h F n, blockEmbedding_mem_upperUnipotent h F n⟩ : ℂ) =
      ∏ i, (inverseStandardCharacter ψ (m i) (n i) : ℂ) := by
  rw [inverseStandardCharacter_eq_prod F h ψ]
  have hlevi : ∀ i, (⟨unipotentLevi h
      ⟨blockEmbedding h F n, blockEmbedding_mem_upperUnipotent h F n⟩ i,
        unipotentLevi_mem h _ i⟩ : upperUnipotent (m i + 1) F) = n i :=
    fun i => Subtype.ext (unipotentLevi_blockEmbedding h F n i)
  have hcorner : unipotentCorner h
      ⟨blockEmbedding h F n, blockEmbedding_mem_upperUnipotent h F n⟩
        (Fin.last (m 0)) 0 = 0 :=
    blockEmbedding_index_zero_one h F n _ _
  simp only [hlevi, hcorner, AddChar.map_zero_eq_one, inv_one, mul_one]

/-- Left translation by `diag(n_0, n_1)` multiplies the scalar section at the Levi identity
by the ambient inverse standard character of `diag(n_0, n_1)`. -/
theorem scalarSection_blockEmbedding_mul_eq_inverseStandardCharacter (f : Sections F h σ)
    (n : BlockUnipotents m F) (g : GeneralLinear (t + 1) F) :
    scalarSection (fun i => (ell i).val) f (blockEmbedding h F n * g) 1 =
      (inverseStandardCharacter ψ t
          ⟨blockEmbedding h F n, blockEmbedding_mem_upperUnipotent h F n⟩ : ℂ) *
        scalarSection (fun i => (ell i).val) f g 1 := by
  rw [inverseStandardCharacter_blockEmbedding, scalarSection_blockEmbedding_mul]

end Covariance

/-! ### The scalar function and its descent -/

section Integrand

variable (ell : ∀ i, Whittaker.glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : RankinSelberg.WhittakerFunctions ψ t)
variable (Φ : SchwartzBruhat (Fin (t + 1) → F))

/-- The scalar function `g ↦ W(g) ⟨f(g), ⊗ ℓ_i⟩ Φ(lastRow g)` on `GL_(t+1)`, before
descent. -/
def groupIntegrand (g : GeneralLinear (t + 1) F) : ℂ :=
  Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 * Φ (RankinSelberg.lastRow g)

theorem groupIntegrand_def (g : GeneralLinear (t + 1) F) :
    groupIntegrand ell f Wtest Φ g =
      Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 * Φ (RankinSelberg.lastRow g) :=
  rfl

/-- Left `H`-invariance: the standard character of `diag(n_0, n_1)` from `W` cancels the
inverse character from the scalar section, and the last row is unchanged. -/
theorem groupIntegrand_blockUnipotent_mul (u : blockUnipotent h F)
    (g : GeneralLinear (t + 1) F) :
    groupIntegrand ell f Wtest Φ (u.val * g) = groupIntegrand ell f Wtest Φ g := by
  obtain ⟨_, n, rfl⟩ := u
  let v : upperUnipotent (t + 1) F :=
    ⟨blockEmbedding h F n, blockEmbedding_mem_upperUnipotent h F n⟩
  have hW : Wtest.val (blockEmbedding h F n * g) =
      (standardCharacter ψ t v : ℂ) * Wtest.val g :=
    Wtest.property v g
  have hrow : RankinSelberg.lastRow (blockEmbedding h F n * g) =
      RankinSelberg.lastRow g :=
    RankinSelberg.lastRow_unipotent_mul v g
  have hchar : (standardCharacter ψ t v : ℂ) * (inverseStandardCharacter ψ t v : ℂ) = 1 :=
    Units.mul_inv (standardCharacter ψ t v)
  change Wtest.val (blockEmbedding h F n * g) *
      scalarSection (fun i => (ell i).val) f (blockEmbedding h F n * g) 1 *
        Φ (RankinSelberg.lastRow (blockEmbedding h F n * g)) =
    Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 * Φ (RankinSelberg.lastRow g)
  rw [hW, hrow, scalarSection_blockEmbedding_mul_eq_inverseStandardCharacter ell f n g]
  calc (standardCharacter ψ t v : ℂ) * Wtest.val g *
        ((inverseStandardCharacter ψ t v : ℂ) * scalarSection (fun i => (ell i).val) f g 1) *
          Φ (RankinSelberg.lastRow g) =
        ((standardCharacter ψ t v : ℂ) * (inverseStandardCharacter ψ t v : ℂ)) *
          (Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 *
            Φ (RankinSelberg.lastRow g)) := by ring
    _ = _ := by rw [hchar, one_mul]

/-- The integrand of the first Section 4.6 unfolding on the actual quotient
`N_(t_1,t_2) \ GL_(t+1)`: the actual descent of `groupIntegrand`. No coset representative
is chosen. -/
def integrand : BlockQuotient h F → ℂ :=
  descend (blockUnipotent h F) (groupIntegrand ell f Wtest Φ)
    (groupIntegrand_blockUnipotent_mul ell f Wtest Φ)

/-- Representative formula: `integrand [g]_H = W(g) ⟨f(g), ⊗ ℓ_i⟩ Φ(lastRow g)`. -/
@[simp]
theorem integrand_mk (g : GeneralLinear (t + 1) F) :
    integrand ell f Wtest Φ (Quotient.mk _ g) =
      Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 * Φ (RankinSelberg.lastRow g) :=
  rfl

/-- The fiber formula: at `[u(x) g]_H` the standard covariance of `W` on the upper
radical `u(x)` supplies the positive kernel `ψ(x_(m 0, 0))` of the raw Jacquet integrand. -/
theorem integrand_fiberPoint (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F) :
    integrand ell f Wtest Φ (fiberPoint h F x g) =
      Wtest.val g * Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g x *
        Φ (RankinSelberg.lastRow g) := by
  let v : upperUnipotent (t + 1) F :=
    ⟨upperRadical h F x, upperRadical_mem_upperUnipotent h F x⟩
  have hW : Wtest.val (upperRadical h F x * g) = positiveKernel ψ x * Wtest.val g := by
    rw [positiveKernel_eq_superdiagonal_upperRadical ψ h x]
    exact Wtest.property v g
  have hrow : RankinSelberg.lastRow (upperRadical h F x * g) =
      RankinSelberg.lastRow g :=
    RankinSelberg.lastRow_unipotent_mul v g
  rw [fiberPoint_def, integrand_mk, hW, hrow, Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand_def]
  ring

/-! ### The fiber integral and the radical average -/

variable [MeasurableSpace F]

/-- The total fiber integral of the integrand over the rectangle, at a representative `g`,
is `W(g) J(f)(g) Φ(lastRow g)` for the ordinary Bochner integral `J(f)(g)` of (4.6.2)
against the same measure. This is an identity of total integrals: no integrability is
assumed. -/
theorem fiberIntegral_integrand
    (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
    (g : GeneralLinear (t + 1) F) :
    fiberIntegral F h μ (integrand ell f Wtest Φ) g =
      Wtest.val g * jacquetFunction ψ (fun i => (ell i).val) μ f g *
        Φ (RankinSelberg.lastRow g) := by
  simp only [fiberIntegral_def, integrand_fiberPoint, jacquetFunction_def]
  rw [integral_mul_const, integral_const_mul]

/-- The published radical average of the integrand at `[g]_N` is
`W(g) J(f)(g) Φ(lastRow g)`, for every Borel additive Haar measure on the rectangle.
This is an identity of total integrals: no integrability is assumed. -/
theorem radicalAverage_integrand_mk :
    ∀ [BorelSpace F]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μ.IsAddHaarMeasure]
      (g : GeneralLinear (t + 1) F),
      radicalAverage F h μ (integrand ell f Wtest Φ) (Quotient.mk _ g) =
        Wtest.val g * jacquetFunction ψ (fun i => (ell i).val) μ f g *
          Φ (RankinSelberg.lastRow g) := by
  intro _ μ _ g
  rw [radicalAverage_mk, ← fiberIntegral_def, fiberIntegral_integrand]

end Integrand

end Langlands.AllField.RankinSelberg.TwoBlockUnfolding
