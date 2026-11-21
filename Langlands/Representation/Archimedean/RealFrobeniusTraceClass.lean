import Langlands.HarmonicAnalysis.Distribution.RealGeneralLinear
import Langlands.Representation.Archimedean.RealPrincipalSeriesFrobeniusClosure
import Langlands.Representation.Archimedean.RealPrincipalSeriesTraceClass

/-! # Trace class of integrated real tests on the Frobenius closure -/

noncomputable section

open MeasureTheory
open scoped ContDiff Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

open Langlands.Analysis.OperatorIdeals
open Langlands.HarmonicAnalysis.RealGeneralLinearDistribution (Test)

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Restrict a real test to the units and regard its values as complex scalars. -/
def complexRestriction (φ : Test n) : C(GL, ℂ) :=
  ⟨fun g => (φ (g : Mat) : ℂ), Complex.continuous_ofReal.comp
    (φ.continuous.comp Units.continuous_val)⟩

theorem hasCompactSupport_complexRestriction (φ : Test n) :
    HasCompactSupport (complexRestriction φ) := by
  have h : tsupport φ ⊆ Set.range (Units.val : GL → Mat) := by
    rw [range_val_eq_setOf_isUnit]
    exact φ.tsupport_subset
  apply HasCompactSupport.of_support_subset_isCompact
    (Units.isOpenEmbedding_val.isInducing.isCompact_preimage' φ.hasCompactSupport h)
  intro g hg
  apply subset_tsupport φ
  exact fun he => hg (by change (φ (g : Mat) : ℂ) = 0; rw [he, Complex.ofReal_zero])

theorem unitsExtension_complexRestriction (φ : Test n) :
    unitsExtension (complexRestriction φ) = fun y : Mat => (φ y : ℂ) := by
  funext y
  by_cases hy : IsUnit y
  · calc
      unitsExtension (complexRestriction φ) y = complexRestriction φ hy.unit := by
        rw [← unitsExtension_val (complexRestriction φ) hy.unit, hy.unit_spec]
      _ = (φ y : ℂ) := by
        change (φ (hy.unit : Mat) : ℂ) = (φ y : ℂ)
        rw [hy.unit_spec]
  · rw [unitsExtension, dite_eq_right hy, φ.zero_on_compl hy]
    exact Complex.ofReal_zero.symm

local instance : SecondCountableTopology GL := Units.isOpenEmbedding_val.secondCountableTopology

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ℓ : V →ₗ[ℂ] ℂ} {a : Fin n → ℂ} {e : Fin n → Fin 2}
  (hgk : IsRealGKModule n ρ π) (hℓ : IsRealJacquetFunctional n ρ π ℓ a e)

local notation "W" => (frobeniusClosure hgk hℓ : Type)
local notation "R" => frobeniusClosureRepresentation hgk hℓ

variable [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  (μ : Measure (Langlands.GeneralLinear n ℝ)) [IsFiniteMeasureOnCompacts μ]

/-- The integrated action of a real test on the Frobenius closure is the orthogonal
compression of its integrated action on the ambient principal series. -/
theorem integrated_frobeniusClosure_eq_compression (φ : Test n)
    (T : Hilbert a e →L[ℂ] Hilbert a e) (S : W →L[ℂ] W)
    (hT : ∀ x, T x = ∫ g : GL, complexRestriction φ g • representation a e g x ∂μ)
    (hS : ∀ x, S x = ∫ g : GL, complexRestriction φ g • R g x ∂μ) :
    S = (((frobeniusClosure hgk hℓ).orthogonalProjectionOnto).comp T).comp
      (frobeniusClosure hgk hℓ).subtypeL := by
  let J := (frobeniusClosure hgk hℓ).subtypeL
  let P := (frobeniusClosure hgk hℓ).orthogonalProjectionOnto
  apply ContinuousLinearMap.ext
  intro x
  have hJ : J (S x) = T (J x) := by
    let F : GL → W := fun g => complexRestriction φ g • R g x
    have hA : Continuous (fun p : GL × W => R p.1 p.2) :=
      isContinuousRepresentation_frobeniusClosureRepresentation hgk hℓ
    have hOrbit : Continuous (fun g : GL => R g x) := by
      simpa only [Function.comp_def, id_eq] using hA.comp (continuous_id.prodMk continuous_const)
    have hF : Continuous F := (complexRestriction φ).continuous.smul hOrbit
    let : NormedAddCommGroup W := Submodule.normedAddCommGroup (frobeniusClosure hgk hℓ)
    have hI : Integrable F μ := hF.integrable_of_hasCompactSupport (f := F)
      (hasCompactSupport_complexRestriction φ).smul_right
    calc
      J (S x) = J (∫ g, F g ∂μ) := congrArg J (hS x)
      _ = ∫ g, J (F g) ∂μ := (J.integral_comp_comm hI).symm
      _ = T (J x) := by
        rw [hT]
        exact integral_congr_ae (Filter.Eventually.of_forall fun g => J.map_smul _ _)
  change S x = P (T (J x))
  rw [← hJ]
  exact ((frobeniusClosure hgk hℓ).orthogonalProjectionOnto_mem_subspace_eq_self (S x)).symm

variable [SFinite μ] [μ.IsMulRightInvariant] [μ.IsMulLeftInvariant]

/-- A bounded operator with the integrated action of a real test on the Frobenius
closure is trace class, given the corresponding ambient integrated operator. -/
theorem isTraceClass_integrated_frobeniusClosure (φ : Test n)
    (T : Hilbert a e →L[ℂ] Hilbert a e) (S : W →L[ℂ] W)
    (hT : ∀ x, T x = ∫ g : GL, complexRestriction φ g • representation a e g x ∂μ)
    (hS : ∀ x, S x = ∫ g : GL, complexRestriction φ g • R g x ∂μ) :
    IsTraceClass (E := W) S := by
  have hsmooth : ContDiff ℝ ∞ (unitsExtension (complexRestriction φ)) := by
    rw [unitsExtension_complexRestriction]
    exact Complex.ofRealCLM.contDiff.comp φ.contDiff
  have h := isTraceClass_integrated μ a (complexRestriction φ) e
    (hasCompactSupport_complexRestriction φ) hsmooth T hT
  rw [integrated_frobeniusClosure_eq_compression hgk hℓ μ φ T S hT hS]
  exact isTraceClass_sandwich T _ _ h

end Langlands.Archimedean.RealPrincipalSeriesHilbert
