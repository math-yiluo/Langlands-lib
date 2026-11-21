import Langlands.Global.ArchimedeanConvolution
import Langlands.TraceFormula.CyclicSplitCenterMeasureStatement
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.LocallyConstant.Basic

/-! # Compact smooth adelic matrix tests and their positive-centre average -/

noncomputable section

universe u

open MeasureTheory
open scoped NNReal
open Langlands.Global

namespace Langlands.TraceFormula

variable (E : Type u) [Field E] [NumberField E] (n : ℕ)

/-- Compactly supported locally constant tests on the actual finite adelic group. -/
abbrev CompactFiniteGLTest :=
  { b : LocallyConstant (FiniteAdelicGL E n) ℂ // HasCompactSupport (b : FiniteAdelicGL E n → ℂ) }

/-- A factorizable test, using the actual projections of the adelic matrix group. -/
def adelicTestTensor (a : ArchimedeanGL.SmoothCompactKernel E n) (b : CompactFiniteGLTest E n) :
    AdelicGL E n → ℂ :=
  fun g => ArchimedeanGL.kernelToContinuousMap E n a (AdelicGL.infinite E n g) *
    b.val (AdelicGL.finite E n g)

/-- The span of the compact smooth archimedean and compact locally constant finite tensors.
Elements are actual functions, not tensor presentations. -/
def compactSmoothAdelicGLTestSpace : Submodule ℂ (AdelicGL E n → ℂ) :=
  Submodule.span ℂ { f | ∃ a b, f = adelicTestTensor E n a b }

abbrev CompactSmoothAdelicGLTest := ↥(compactSmoothAdelicGLTestSpace E n)

/-- A tensor defines a test in the span. -/
def CompactSmoothAdelicGLTest.tensor (a : ArchimedeanGL.SmoothCompactKernel E n)
    (b : CompactFiniteGLTest E n) : CompactSmoothAdelicGLTest E n :=
  ⟨adelicTestTensor E n a b, Submodule.subset_span ⟨a, b, rfl⟩⟩

private theorem continuous_tensor (a : ArchimedeanGL.SmoothCompactKernel E n)
    (b : CompactFiniteGLTest E n) : Continuous (adelicTestTensor E n a b) :=
  ((ArchimedeanGL.kernelToContinuousMap E n a).continuous.comp
    (AdelicGL.infinite E n).continuous).mul (b.val.continuous.comp (AdelicGL.finite E n).continuous)

private theorem compactSupport_tensor (a : ArchimedeanGL.SmoothCompactKernel E n)
    (b : CompactFiniteGLTest E n) : HasCompactSupport (adelicTestTensor E n a b) := by
  let e := (AdelicGL.split E n).toHomeomorph
  let U := tsupport (ArchimedeanGL.kernelToContinuousMap E n a : InfiniteAdelicGL E n → ℂ)
  let V := tsupport (b.val : FiniteAdelicGL E n → ℂ)
  have hU : IsCompact U := a.property
  have hV : IsCompact V := b.property
  have hUV : IsCompact (e ⁻¹' (U ×ˢ V)) := e.isCompact_preimage.mpr (hU.prod hV)
  apply hUV.of_isClosed_subset isClosed_closure
  apply closure_minimal _ ((isClosed_closure.prod isClosed_closure).preimage e.continuous)
  intro g hg
  change adelicTestTensor E n a b g ≠ 0 at hg
  exact ⟨subset_closure (show _ ≠ 0 from (mul_ne_zero_iff.mp hg).1),
    subset_closure (show _ ≠ 0 from (mul_ne_zero_iff.mp hg).2)⟩

theorem CompactSmoothAdelicGLTest.continuous (f : CompactSmoothAdelicGLTest E n) :
    Continuous f.val := by
  apply Submodule.span_induction (p := fun f _ => Continuous f) _ _ _ _ f.property
  · rintro _ ⟨a, b, rfl⟩
    exact continuous_tensor E n a b
  · exact continuous_const
  · exact fun _ _ _ _ hf hg => hf.add hg
  · exact fun c _ _ hf => continuous_const.smul hf

theorem CompactSmoothAdelicGLTest.hasCompactSupport (f : CompactSmoothAdelicGLTest E n) :
    HasCompactSupport f.val := by
  apply Submodule.span_induction (p := fun f _ => HasCompactSupport f) _ _ _ _ f.property
  · rintro _ ⟨a, b, rfl⟩
    exact compactSupport_tensor E n a b
  · exact HasCompactSupport.zero
  · exact fun _ _ _ _ hf hg => hf.add hg
  · exact fun _ _ _ hf => hf.smul_left

/-- The ordinary trivial-character split-centre average, written as a function on
representatives. The Haar measure in the logarithmic scalar coordinate is supplied. -/
def CompactSmoothAdelicGLTest.centralAverage (f : CompactSmoothAdelicGLTest E n) (da : Measure ℝ) :
    AdelicGL E n → ℂ :=
  fun g => ∫ x, f.val (adelicPositiveScalar E n (PositiveRealTorus.expUnit x) * g) ∂da

theorem CompactSmoothAdelicGLTest.centralAverage_scalar_mul
    (f : CompactSmoothAdelicGLTest E n) (da : Measure ℝ) [da.IsAddRightInvariant]
    (a : ℝ≥0ˣ) (g : AdelicGL E n) :
    CompactSmoothAdelicGLTest.centralAverage E n f da (adelicPositiveScalar E n a * g) =
      CompactSmoothAdelicGLTest.centralAverage E n f da g := by
  let y := Real.log ((a : ℝ≥0) : ℝ)
  have ha : PositiveRealTorus.expUnit y = a := PositiveRealTorus.expUnit_log a
  have hy (x : ℝ) : PositiveRealTorus.expUnit (x + y) =
      PositiveRealTorus.expUnit x * a := by
    apply Units.ext
    apply NNReal.coe_injective
    rw [Units.val_mul, NNReal.coe_mul, PositiveRealTorus.coe_expUnit,
      PositiveRealTorus.coe_expUnit, Real.exp_add, ← PositiveRealTorus.coe_expUnit y, ha]
  simp only [CompactSmoothAdelicGLTest.centralAverage, ← mul_assoc, ← map_mul, ← hy]
  exact integral_add_right_eq_self
    (fun x => f.val (adelicPositiveScalar E n (PositiveRealTorus.expUnit x) * g)) y

end Langlands.TraceFormula
