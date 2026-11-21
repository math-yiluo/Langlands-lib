import Langlands.Representation.Archimedean.HilbertGlobalizationStatement
import Langlands.Representation.Archimedean.RealFrobeniusHilbertAdmissibility
import Langlands.Representation.Archimedean.RealFrobeniusSmoothDensity
import Langlands.Representation.Archimedean.RealSmoothKernelCharacter
import Langlands.Representation.Archimedean.SmoothHilbertExponential

/-! # The smooth realization and trace character of the real Frobenius closure -/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

open Langlands.Analysis.OperatorIdeals
open Langlands.HarmonicAnalysis.RealGeneralLinearDistribution
open RealPrincipalSeriesDuality

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] measurableSpaceK borelSpaceK

universe uV

variable {n : ℕ} {a : Fin n → ℂ} {eps : Fin n → Fin 2}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "I" => matrixModel ℝ n
local notation "K" => unitaryCompact ℝ n

private theorem norm_representation_compact (k : K) (x : Hilbert a eps) :
    ‖representation a eps (k : GL) x‖ = ‖x‖ := by
  have h := (denseRange_embed a eps).equalizer
    ((representation a eps (k : GL)).continuous.norm) continuous_norm
    (funext fun f => by
      change ‖representation a eps (k : GL) (embed a eps f)‖ = ‖embed a eps f‖
      rw [representation_embed, ← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero]
      change ‖restrictToL2 a eps (translation a eps (k : GL) f)‖ ^ 2 =
        ‖restrictToL2 a eps f‖ ^ 2
      rw [restrictToL2_norm_sq, restrictToL2_norm_sq]
      simp only [translation_apply]
      exact integral_mul_right_eq_self (μ := haarK n) (fun h : K => ‖f.1 (h : GL)‖ ^ 2) k)
  exact congrFun h x

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ℓ : V →ₗ[ℂ] ℂ}
  (hgk : IsRealGKModule n ρ π) (hℓ : IsRealJacquetFunctional n ρ π ℓ a eps)

local notation "S" => frobeniusClosure hgk hℓ
local notation "W" => (S : Type)
local notation "R" => frobeniusClosureRepresentation hgk hℓ
local notation "hR" => isContinuousRepresentation_frobeniusClosureRepresentation hgk hℓ

set_option maxHeartbeats 1000000 in
/-- The Frobenius closure realizes the original irreducible admissible GK module
in its genuine smooth compact-finite subspace with all globalization compatibilities. -/
theorem exists_frobeniusEquiv_globalization (hirr : IsIrreducibleGKModule ρ π)
    (hadm : IsAdmissibleGKModule ρ) (h₀ : ℓ ≠ 0) :
    ∃ e : V ≃ₗ[ℂ] smoothHilbertKFinite ℝ n (H := W) R,
      IsSmoothHilbertGlobalization ℝ n (H := W) R ρ π e := by
  let e : V ≃ₗ[ℂ] smoothHilbertKFinite ℝ n (H := W) R := frobeniusKFiniteEquiv hgk hℓ hirr h₀
  let globalizationMap := @smoothHilbertGlobalizationMap ℝ _ n W
    (Submodule.normedAddCommGroup S) (Submodule.innerProductSpace S)
  let j := @globalizationMap R V ‹AddCommGroup V› ‹Module ℂ V› e
  have he : j = frobeniusSmoothMap hgk hℓ := rfl
  refine ⟨e, ⟨hR, isTopologicallyIrreducible_frobeniusClosureRepresentation hgk hℓ hirr h₀,
    isAdmissible_frobeniusClosureRepresentation hgk hℓ hirr h₀ hadm⟩, ?_, ?_, ?_,
    hasSmoothHilbertExponentialDerivatives ℝ n (H := W) R⟩
  · change DenseRange j
    rw [he]
    exact denseRange_frobeniusSmoothMap hgk hℓ
  · intro k v
    change j (ρ k v) = DerivativeSmoothVectors.representation I (E := W) R (Unitary.toUnits k) (j v)
    rw [he]
    exact frobeniusSmoothMap_compact hgk hℓ k v
  · intro X v
    change j (π (1 ⊗ₜ X) v) = DerivativeSmoothVectors.operator I (E := W) R X (j v)
    rw [he]
    exact frobeniusSmoothMap_lie hgk hℓ X v

/-- The compact action preserves the Frobenius Hilbert inner product. -/
theorem inner_frobeniusClosureRepresentation_compact (k : K) (x y : W) :
    ⟪R (k : GL) x, R (k : GL) y⟫_ℂ = ⟪x, y⟫_ℂ := by
  change ⟪representation a eps (k : GL) (x : Hilbert a eps),
      representation a eps (k : GL) (y : Hilbert a eps)⟫_ℂ =
    ⟪(x : Hilbert a eps), (y : Hilbert a eps)⟫_ℂ
  exact ((LinearMap.norm_map_iff_inner_map_map (representation a eps (k : GL))).mp
    (norm_representation_compact k)) _ _

variable [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  (μ : Measure (Langlands.GeneralLinear n ℝ)) [IsFiniteMeasureOnCompacts μ]

local notation "WNorm" => Submodule.normedAddCommGroup S
local notation "WInner" => Submodule.innerProductSpace S
local notation "WComplete" =>
  IsComplete.completeSpace_coe (IsClosed.isComplete (isClosed_frobeniusClosure hgk hℓ))

set_option maxHeartbeats 600000 in
/-- The ordinary real integrated action on the Frobenius Hilbert closure. -/
def frobeniusRealTestOperator :=
  @realIntegratedOperator n _ _ μ _ W WNorm WInner WComplete R hR

theorem frobeniusRealTestOperator_apply (φ : Test n) (x : W) :
    frobeniusRealTestOperator hgk hℓ μ φ x = ∫ g : GL, (φ (g : Mat) : ℂ) • R g x ∂μ :=
  @realIntegratedOperator_apply n _ _ μ _ W WNorm WInner WComplete R hR φ x

variable [SFinite μ] [μ.IsMulRightInvariant] [μ.IsMulLeftInvariant]

set_option maxHeartbeats 700000 in
theorem isTraceClass_frobeniusRealTestOperator (φ : Test n) :
    @IsTraceClass W WNorm WInner WComplete (frobeniusRealTestOperator hgk hℓ μ φ) := by
  let P := closureSubmodule a eps
  let E := Hilbert a eps
  let nE : NormedAddCommGroup E := Submodule.normedAddCommGroup P
  let iE : InnerProductSpace ℂ E := Submodule.innerProductSpace P
  have cE : CompleteSpace E := inferInstanceAs (CompleteSpace (Hilbert a eps))
  let A := @realIntegratedOperator n _ _ μ _ E nE iE cE
    (representation a eps) (isContinuousRepresentation a eps)
  have hA := @realIntegratedOperator_apply n _ _ μ _ E nE iE cE
    (representation a eps) (isContinuousRepresentation a eps) φ
  exact isTraceClass_integrated_frobeniusClosure hgk hℓ μ φ (A φ)
    (frobeniusRealTestOperator hgk hℓ μ φ) hA (frobeniusRealTestOperator_apply hgk hℓ μ φ)

set_option maxHeartbeats 600000 in
/-- The character of the real Hilbert Frobenius representation as a distribution
on the open real general linear group. -/
def frobeniusCharacter : Distribution n :=
  @realHilbertCharacter n _ _ μ _ W WNorm WInner R hR WComplete
    (frobeniusRealTestOperator hgk hℓ μ)
    (frobeniusRealTestOperator_apply hgk hℓ μ)
    (isTraceClass_frobeniusRealTestOperator hgk hℓ μ)

set_option maxHeartbeats 600000 in
theorem isConjugationInvariant_frobeniusCharacter :
    IsConjugationInvariant (frobeniusCharacter hgk hℓ μ) :=
  @isConjugationInvariant_realHilbertCharacter n _ _ μ _ W WNorm WInner R hR WComplete
    (frobeniusRealTestOperator hgk hℓ μ)
    (frobeniusRealTestOperator_apply hgk hℓ μ)
    (isTraceClass_frobeniusRealTestOperator hgk hℓ μ) _ _

end Langlands.Archimedean.RealPrincipalSeriesHilbert
