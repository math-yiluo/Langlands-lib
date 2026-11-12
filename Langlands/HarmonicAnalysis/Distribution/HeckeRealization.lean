import Langlands.HarmonicAnalysis.Distribution.Haar
import Langlands.HarmonicAnalysis.Distribution.TopologicalSupport
import Langlands.Representation.Hecke.Convolution

/-! # Renard II.3.12–II.3.13: the existing Hecke algebra in distributions -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- The actual density realization of the already published Haar Hecke algebra. -/
def heckeDistribution : Hecke.HeckeAlgebra μ →ₗ[ℂ] Distribution G :=
  (testDensity μ).comp (Hecke.HeckeAlgebra.toTestFunction μ).toLinearMap

omit [Group G] [IsTopologicalGroup G] in
@[simp]
theorem heckeDistribution_apply (h : Hecke.HeckeAlgebra μ) (f : SchwartzBruhat G) :
    heckeDistribution μ h f = ∫ x, h x * f x ∂μ := rfl

/-- Renard's distribution subspace H(G), realized as the actual density range.
The existing Hecke algebra remains the function model and algebra carrier. -/
def heckeDistributionSpace : Submodule ℂ (Distribution G) :=
  LinearMap.range (heckeDistribution μ)

/-- The transpose of `f ↦ f * check(h)`, with h in the existing Hecke algebra.
In this test-kernel expression the integral uses left Haar μ. -/
def rightHeckeOperator (h : Hecke.HeckeAlgebra μ) : Module.End ℂ (Distribution G) where
  toFun T := T.comp ((Hecke.TestFunction.convolutionBilinear μ).flip
    (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ h)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The transpose of `f ↦ check(h) * f`. The inverse measure is essential here:
it implements inversion of the distribution h μ in every topological group. -/
def leftHeckeOperator (h : Hecke.HeckeAlgebra μ) : Module.End ℂ (Distribution G) where
  toFun T := T.comp (Hecke.TestFunction.convolutionBilinear μ.inv
    (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ h)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The source's T*h for arbitrary algebraic distributions. -/
abbrev rightHeckeConvolution (T : Distribution G) (h : Hecke.HeckeAlgebra μ) :
    Distribution G := rightHeckeOperator μ h T

/-- The source's h*T for arbitrary algebraic distributions. -/
abbrev leftHeckeConvolution (h : Hecke.HeckeAlgebra μ) (T : Distribution G) :
    Distribution G := leftHeckeOperator μ h T

@[simp]
theorem rightHeckeConvolution_apply (T : Distribution G) (h : Hecke.HeckeAlgebra μ)
    (f : SchwartzBruhat G) :
    rightHeckeConvolution μ T h f = T (Hecke.TestFunction.convolution μ f
      (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ h))) := rfl

@[simp]
theorem leftHeckeConvolution_apply (h : Hecke.HeckeAlgebra μ) (T : Distribution G)
    (f : SchwartzBruhat G) :
    leftHeckeConvolution μ h T f = T (Hecke.TestFunction.convolution μ.inv
      (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ h)) f) := rfl

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- The original full distributions whose every right Hecke product is compact. -/
def rightEssentiallyCompact : Submodule ℂ (Distribution G) where
  carrier := {T | ∀ h : Hecke.HeckeAlgebra μ,
    rightHeckeConvolution μ T h ∈ compactlySupported}
  zero_mem' := by
    intro h
    change rightHeckeOperator μ h 0 ∈ compactlySupported
    rw [map_zero]
    exact Submodule.zero_mem _
  add_mem' := by
    intro T S hT hS h
    change rightHeckeOperator μ h (T + S) ∈ compactlySupported
    rw [map_add]
    exact Submodule.add_mem _ (hT h) (hS h)
  smul_mem' := by
    intro c T hT h
    change rightHeckeOperator μ h (c • T) ∈ compactlySupported
    rw [map_smul]
    exact Submodule.smul_mem _ c (hT h)

/-- The analogous left-essentially-compact submodule. -/
def leftEssentiallyCompact : Submodule ℂ (Distribution G) where
  carrier := {T | ∀ h : Hecke.HeckeAlgebra μ,
    leftHeckeConvolution μ h T ∈ compactlySupported}
  zero_mem' := by
    intro h
    change leftHeckeOperator μ h 0 ∈ compactlySupported
    rw [map_zero]
    exact Submodule.zero_mem _
  add_mem' := by
    intro T S hT hS h
    change leftHeckeOperator μ h (T + S) ∈ compactlySupported
    rw [map_add]
    exact Submodule.add_mem _ (hT h) (hS h)
  smul_mem' := by
    intro c T hT h
    change leftHeckeOperator μ h (c • T) ∈ compactlySupported
    rw [map_smul]
    exact Submodule.smul_mem _ c (hT h)

/-- The source's two-sided essentially compact distributions. -/
def essentiallyCompact : Submodule ℂ (Distribution G) :=
  rightEssentiallyCompact μ ⊓ leftEssentiallyCompact μ

end Langlands.HarmonicAnalysis.Distribution
