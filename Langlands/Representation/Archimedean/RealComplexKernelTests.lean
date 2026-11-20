import Langlands.HarmonicAnalysis.Distribution.RealGeneralLinear
import Langlands.Representation.Archimedean.PrincipalSeriesStability

/-! # Decomposition of smooth complex kernels into real matrix tests -/

noncomputable section

open Filter Set
open scoped ContDiff Distributions Manifold Matrix Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.HarmonicAnalysis.RealGeneralLinearDistribution

variable {n : ℕ}

local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Mdl" => matrixModel ℝ n

private theorem support_unitsExtension_subset (f : GL → ℂ) :
    Function.support (unitsExtension f) ⊆ (Units.val : GL → Mat) '' tsupport f := by
  intro y hy
  by_cases hu : IsUnit y
  · have h : f hu.unit ≠ 0 := by
      have he := unitsExtension_val f hu.unit
      rw [hu.unit_spec] at he
      exact he ▸ hy
    exact ⟨hu.unit, subset_tsupport f h, hu.unit_spec⟩
  · exact (hy (by rw [unitsExtension, dite_eq_right hu])).elim

private theorem tsupport_unitsExtension_subset (f : GL → ℂ) (hf : HasCompactSupport f) :
    tsupport (unitsExtension f) ⊆ (Units.val : GL → Mat) '' tsupport f :=
  closure_minimal (support_unitsExtension_subset f) (hf.image Units.continuous_val).isClosed

private theorem tsupport_unitsExtension_subset_units (f : GL → ℂ) (hf : HasCompactSupport f) :
    tsupport (unitsExtension f) ⊆ (matrixOpen n : Set Mat) := by
  intro y hy
  obtain ⟨g, -, rfl⟩ := tsupport_unitsExtension_subset f hf hy
  exact g.isUnit

private theorem contDiff_unitsExtension_of_compact (f : GL → ℂ)
    (hfc : HasCompactSupport f) (hf : ContMDiff Mdl 𝓘(ℝ, ℂ) ∞ f) :
    ContDiff ℝ ∞ (unitsExtension f) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hu : IsUnit y
  · exact (contDiffOn_unitsExtension hf).contDiffAt (Units.isOpen.mem_nhds hu)
  · have hy : y ∉ tsupport (unitsExtension f) :=
      fun h => hu (tsupport_unitsExtension_subset_units f hfc h)
    have hz : ContDiffAt ℝ ∞ (fun _ : Mat => (0 : ℂ)) y := contDiffAt_const
    apply hz.congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport (unitsExtension f)).isOpen_compl.mem_nhds hy] with z hz
    exact image_eq_zero_of_notMem_tsupport hz

/-- Extend a compactly supported smooth complex kernel by zero to a test on
the open invertible matrices. -/
def complexTestOfCompactKernel (f : GL → ℂ)
    (hfc : HasCompactSupport f) (hf : ContMDiff Mdl 𝓘(ℝ, ℂ) ∞ f) : 𝓓(matrixOpen n, ℂ) where
  toFun := unitsExtension f
  contDiff' := contDiff_unitsExtension_of_compact f hfc hf
  hasCompactSupport' := (hfc.image Units.continuous_val).of_isClosed_subset
    (isClosed_tsupport (unitsExtension f)) (tsupport_unitsExtension_subset f hfc)
  tsupport_subset' := tsupport_unitsExtension_subset_units f hfc

/-- A compactly supported smooth complex function on the real units is the
sum of two real matrix tests with coefficients `1` and `I`. -/
theorem exists_realTests_of_compactSmoothKernel (f : GL → ℂ)
    (hfc : HasCompactSupport f) (hf : ContMDiff Mdl 𝓘(ℝ, ℂ) ∞ f) :
    ∃ φ ψ : Test n, ∀ g : GL, f g = (φ (g : Mat) : ℂ) + Complex.I * (ψ (g : Mat) : ℂ) := by
  let h := complexTestOfCompactKernel f hfc hf
  refine ⟨TestFunction.postcompCLM Complex.reCLM h, TestFunction.postcompCLM Complex.imCLM h, ?_⟩
  intro g
  change f g = (Complex.reCLM (unitsExtension f (g : Mat)) : ℂ) +
    Complex.I * (Complex.imCLM (unitsExtension f (g : Mat)) : ℂ)
  rw [unitsExtension_val, Complex.reCLM_apply, Complex.imCLM_apply, mul_comm Complex.I]
  exact (Complex.re_add_im (f g)).symm

end Langlands.Archimedean
