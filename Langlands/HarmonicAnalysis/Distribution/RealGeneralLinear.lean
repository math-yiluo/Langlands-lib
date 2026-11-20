import Langlands.Group.GL.Basic
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Real distributions on the open general linear group -/

noncomputable section

open Set TopologicalSpace
open scoped Distributions Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis.RealGeneralLinearDistribution

private def precomposeTest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (A : E ≃L[ℝ] E) (hA : ∀ x, A x ∈ Ω ↔ x ∈ Ω)
    (f : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) where
  toFun := f ∘ A
  contDiff' := f.contDiff.comp A.toContinuousLinearMap.contDiff
  hasCompactSupport' := by
    change IsCompact (closure (A.toHomeomorph ⁻¹' Function.support f))
    rw [← A.toHomeomorph.preimage_closure]
    exact A.toHomeomorph.isCompact_preimage.mpr f.hasCompactSupport
  tsupport_subset' := by
    change closure (A.toHomeomorph ⁻¹' Function.support f) ⊆ Ω
    rw [← A.toHomeomorph.preimage_closure]
    intro x hx
    exact (hA x).mp (f.tsupport_subset hx)

local notation "Mat" n => Matrix (Fin n) (Fin n) ℝ
local notation "GL" n => Langlands.GeneralLinear n ℝ

/-- The real general linear group as an open subset of the real matrix space. -/
def matrixOpen (n : ℕ) : Opens (Mat n) :=
  ⟨{X | IsUnit X}, Units.isOpen⟩

/-- Real scalar smooth compactly supported tests on actual real invertible matrices. -/
abbrev Test (n : ℕ) := 𝓓(matrixOpen n, ℝ)

/-- Complex-valued distributions on actual real invertible matrices. -/
abbrev Distribution (n : ℕ) := 𝓓'(matrixOpen n, ℂ)

private def conjugationEquiv {n : ℕ} (g : GL n) : (Mat n) ≃L[ℝ] (Mat n) :=
  ((g.mulLeftLinearEquiv ℝ (Mat n)).trans ((g⁻¹).mulRightLinearEquiv ℝ)).toContinuousLinearEquiv

private theorem isUnit_conjugationEquiv {n : ℕ} (g : GL n) (X : Mat n) :
    IsUnit (conjugationEquiv g X) ↔ IsUnit X := by
  change IsUnit ((g : Mat n) * X * ((g⁻¹ : GL n) : Mat n)) ↔ IsUnit X
  constructor
  · intro hX
    have h := (g⁻¹ : GL n).isUnit.mul (hX.mul g.isUnit)
    have h₁ : ((g⁻¹ : GL n) : Mat n) * (g : Mat n) = 1 := g.inv_val
    have he : ((g⁻¹ : GL n) : Mat n) * ((g : Mat n) * X * ((g⁻¹ : GL n) : Mat n) * (g : Mat n)) = X := by
      calc
        _ = (((g⁻¹ : GL n) : Mat n) * (g : Mat n)) * X *
              (((g⁻¹ : GL n) : Mat n) * (g : Mat n)) := by simp only [mul_assoc]
        _ = _ := by rw [h₁, one_mul, mul_one]
    exact he ▸ h
  · intro hX
    exact (g.isUnit.mul hX).mul (g⁻¹ : GL n).isUnit

/-- Pull back a real test by actual matrix conjugation `X ↦ g X g⁻¹`. -/
def conjugationTest {n : ℕ} (g : GL n) (f : Test n) : Test n :=
  precomposeTest (conjugationEquiv g) (isUnit_conjugationEquiv g) f

@[simp]
theorem conjugationTest_apply {n : ℕ} (g : GL n) (f : Test n) (X : Mat n) :
    conjugationTest g f X = f ((g : Mat n) * X * ((g⁻¹ : GL n) : Mat n)) := rfl

/-- Pull back a real test by ordinary matrix transpose. -/
def transposeTest {n : ℕ} (f : Test n) : Test n :=
  precomposeTest (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toContinuousLinearEquiv
    (fun X => Matrix.isUnit_transpose (A := X)) f

@[simp]
theorem transposeTest_apply {n : ℕ} (f : Test n) (X : Mat n) :
    transposeTest f X = f Xᵀ := rfl

/-- Invariance under conjugation by every real general linear element. -/
def IsConjugationInvariant {n : ℕ} (D : Distribution n) : Prop :=
  ∀ (g : GL n) (f : Test n), D (conjugationTest g f) = D f

/-- Invariance under ordinary matrix transpose. -/
def IsTransposeInvariant {n : ℕ} (D : Distribution n) : Prop :=
  ∀ f : Test n, D (transposeTest f) = D f

end Langlands.HarmonicAnalysis.RealGeneralLinearDistribution
