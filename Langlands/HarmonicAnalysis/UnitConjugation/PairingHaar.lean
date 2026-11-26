import Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution
import Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier
import Langlands.HarmonicAnalysis.LinearHaarScaling
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # Haar preservation of fixed-unit conjugation -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory
open scoped NNReal

variable (F : Type*) [Field F] {A : Type*} [Ring A] [Algebra F A]

/-- Unit conjugation on the algebra as a linear equivalence. -/
def conjugationLinearEquiv (u : Aˣ) : A ≃ₗ[F] A :=
  (Units.mulLeftLinearEquiv F A u).trans (Units.mulRightLinearEquiv F u⁻¹)

@[simp] theorem conjugationLinearEquiv_apply (u : Aˣ) (x : A) :
    conjugationLinearEquiv F u x = (u : A) * x * ↑u⁻¹ := rfl

variable {F} [FiniteDimensional F A] {B : LinearMap.BilinForm F A}

/-- The determinant of conjugation by a unit has square one when the pairing is
nondegenerate and conjugation invariant. -/
theorem det_conjugationLinearEquiv_mul_self (hB : IsInvariantPairing B) (u : Aˣ) :
    LinearEquiv.det (conjugationLinearEquiv F u) *
      LinearEquiv.det (conjugationLinearEquiv F u) = 1 := by
  let i := B.toDual hB.nondegenerate
  let e := conjugationLinearEquiv F u
  have hi : e.toLinearMap.dualMap.comp (i.conj e.toLinearMap) = LinearMap.id := by
    apply LinearMap.ext
    intro L
    apply LinearMap.ext
    intro a
    change B (e (i.symm L)) (e a) = L a
    rw [conjugationLinearEquiv_apply, conjugationLinearEquiv_apply, hB.conj_invariant]
    exact congrArg (fun z : Module.Dual F A => z a) (i.apply_symm_apply L)
  have hd := congrArg LinearMap.det hi
  rw [LinearMap.det_comp, LinearMap.det_dualMap, LinearMap.det_id] at hd
  have hc : (i.conj e.toLinearMap).det = e.toLinearMap.det := by
    rw [LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj]
  rw [hc] at hd
  apply Units.ext
  simpa only [Units.val_mul, LinearEquiv.coe_det, Units.val_one, e] using hd

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A]

/-- Conjugation preserving a nondegenerate pairing preserves additive Haar
measure, with any normalization. -/
def PairingHaarPreservationStatement (B : LinearMap.BilinForm F A) (μ : Measure A) : Prop :=
  IsInvariantPairing B → ∀ u : Aˣ, MeasurePreserving (conjugationHomeomorph u) μ μ

theorem pairingHaarPreservation (B : LinearMap.BilinForm F A) (μ : Measure A) [μ.IsAddHaarMeasure] :
    PairingHaarPreservationStatement B μ := by
  intro hB u
  let d := LinearEquiv.det (conjugationLinearEquiv F u)
  let χ : Fˣ →* ℝ≥0 := distribHaarChar F
  have hd : d * d = 1 := det_conjugationLinearEquiv_mul_self hB u
  have hχsq : χ d * χ d = 1 := by rw [← map_mul, hd, map_one]
  have hχ : χ d = 1 := by
    apply NNReal.eq
    have h : (χ d : ℝ) * (χ d : ℝ) = 1 := by exact_mod_cast hχsq
    exact (mul_self_inj_of_nonneg (χ d).coe_nonneg (by exact zero_le_one)).mp (by simpa using h)
  refine ⟨(conjugationHomeomorph u).continuous.measurable, ?_⟩
  change μ.map (conjugationLinearEquiv F u) = μ
  rw [map_linearEquiv_addHaar, show distribHaarChar F d = 1 from hχ, inv_one, one_smul]

end Langlands.HarmonicAnalysis.UnitConjugation
