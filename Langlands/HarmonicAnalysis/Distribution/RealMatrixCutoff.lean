import Langlands.HarmonicAnalysis.Distribution.RealTransposeInvariantStatement
import Langlands.HarmonicAnalysis.Distribution.TestCutoff
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Determinant cutoff from real invertible matrices to all matrices -/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis.RealGeneralLinearDistribution

variable {n : ℕ}

local notation "Mat" n => Matrix (Fin n) (Fin n) ℝ
local notation "GL" n => Langlands.GeneralLinear n ℝ

/-- Smooth real tests on the full space of real square matrices. -/
abbrev FullTest (n : ℕ) := 𝓓((⊤ : Opens (Mat n)), ℝ)

/-- Complex-valued distributions on the full space of real square matrices. -/
abbrev FullDistribution (n : ℕ) := 𝓓'((⊤ : Opens (Mat n)), ℂ)

private def pullbackFullTest (A : (Mat n) ≃L[ℝ] (Mat n)) (f : FullTest n) : FullTest n where
  toFun := f ∘ A
  contDiff' := f.contDiff.comp A.toContinuousLinearMap.contDiff
  hasCompactSupport' := by
    change IsCompact (closure (A.toHomeomorph ⁻¹' Function.support f))
    rw [← A.toHomeomorph.preimage_closure]
    exact A.toHomeomorph.isCompact_preimage.mpr f.hasCompactSupport
  tsupport_subset' := subset_univ _

/-- Pull back a test on all matrices by actual general linear conjugation. -/
def fullConjugationTest (g : GL n) (f : FullTest n) : FullTest n :=
  pullbackFullTest (((g.mulLeftLinearEquiv ℝ (Mat n)).trans
    ((g⁻¹).mulRightLinearEquiv ℝ)).toContinuousLinearEquiv) f

@[simp]
theorem fullConjugationTest_apply (g : GL n) (f : FullTest n) (A : Mat n) :
    fullConjugationTest g f A = f ((g : Mat n) * A * ((g⁻¹ : GL n) : Mat n)) := rfl

/-- Pull back a test on all matrices by ordinary matrix transpose. -/
def fullTransposeTest (f : FullTest n) : FullTest n :=
  pullbackFullTest (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toContinuousLinearEquiv f

@[simp]
theorem fullTransposeTest_apply (f : FullTest n) (A : Mat n) :
    fullTransposeTest f A = f Aᵀ := rfl

/-- Conjugation invariance on the full matrix space under the real units. -/
def IsFullConjugationInvariant (D : FullDistribution n) : Prop :=
  ∀ (g : GL n) (f : FullTest n), D (fullConjugationTest g f) = D f

/-- Transpose invariance on the full matrix space. -/
def IsFullTransposeInvariant (D : FullDistribution n) : Prop :=
  ∀ f : FullTest n, D (fullTransposeTest f) = D f

private theorem contDiff_det_real : ContDiff ℝ ∞ (fun A : Mat n => A.det) :=
  Archimedean.RealPrincipalSeriesDuality.contDiff_det ∞

private theorem tsupport_detCutoff_subset {χ : ℝ → ℝ} (hχ : tsupport χ ⊆ {x | x ≠ 0}) :
    tsupport (fun A : Mat n => χ A.det) ⊆ matrixOpen n := by
  have hClosed : IsClosed ((fun A : Mat n => A.det) ⁻¹' tsupport χ) :=
    (isClosed_tsupport χ).preimage contDiff_det_real.continuous
  have hSupport : tsupport (fun A : Mat n => χ A.det) ⊆ (fun A : Mat n => A.det) ⁻¹' tsupport χ :=
    closure_minimal (fun A h => subset_tsupport χ h) hClosed
  intro A hA
  exact (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr (hχ (hSupport hA)))

/-- Multiply a full matrix test by a smooth scalar function of the determinant
whose support avoids zero, obtaining a test on the real units. -/
def detCutoffTestCLM {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ {x | x ≠ 0}) : FullTest n →L[ℝ] Test n :=
  cutoffTestCLM (hχ.comp contDiff_det_real) (matrixOpen n) (tsupport_detCutoff_subset hs)

@[simp]
theorem detCutoffTestCLM_apply {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ {x | x ≠ 0}) (f : FullTest n) (A : Mat n) :
    detCutoffTestCLM hχ hs f A = f A * χ A.det := rfl

theorem detCutoffTestCLM_fullConjugation {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ {x | x ≠ 0}) (g : GL n) (f : FullTest n) :
    detCutoffTestCLM hχ hs (fullConjugationTest g f) =
      conjugationTest g (detCutoffTestCLM hχ hs f) := by
  ext A
  simp only [detCutoffTestCLM_apply, fullConjugationTest_apply, conjugationTest_apply, Matrix.det_units_conj]

theorem detCutoffTestCLM_fullTranspose {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ {x | x ≠ 0}) (f : FullTest n) :
    detCutoffTestCLM hχ hs (fullTransposeTest f) = transposeTest (detCutoffTestCLM hχ hs f) := by
  ext A
  simp only [detCutoffTestCLM_apply, fullTransposeTest_apply, transposeTest_apply, Matrix.det_transpose]

/-- A distribution on the real units extends to all matrices after multiplication
by a smooth determinant cutoff whose support avoids zero. -/
def extendDistributionByDetCutoff (D : Distribution n) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ {x | x ≠ 0}) : FullDistribution n :=
  D.comp (detCutoffTestCLM hχ hs)

theorem isFullConjugationInvariant_extendDistributionByDetCutoff
    (D : Distribution n) (hD : IsConjugationInvariant D) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ {x | x ≠ 0}) :
    IsFullConjugationInvariant (extendDistributionByDetCutoff D hχ hs) := by
  intro g f
  change D (detCutoffTestCLM hχ hs (fullConjugationTest g f)) = D (detCutoffTestCLM hχ hs f)
  rw [detCutoffTestCLM_fullConjugation]
  exact hD g _

private theorem exists_testDetCutoff (φ : Test n) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ {x | x ≠ 0} ∧
      ∀ A ∈ tsupport φ, χ (Matrix.det A) = 1 := by
  let C := (fun A : Mat n => A.det) '' tsupport φ
  have hC : IsCompact C := φ.hasCompactSupport.image contDiff_det_real.continuous
  have hC0 : C ⊆ ({0} : Set ℝ)ᶜ := by
    rintro _ ⟨A, hA, rfl⟩
    have hu : IsUnit A := φ.tsupport_subset hA
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hu)
  obtain ⟨S, hS, hCS, hS0⟩ := exists_compact_between hC isClosed_singleton.isOpen_compl hC0
  obtain ⟨χ, hχ, -, hSupport, hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := ⊤) isOpen_interior hC.isClosed hCS
  refine ⟨χ, hχ, ?_, fun A hA => (hone A.det).mp ⟨A, hA, rfl⟩⟩
  change closure (Function.support χ) ⊆ _
  rw [hSupport]
  exact (closure_minimal interior_subset hS.isClosed).trans hS0

private theorem exists_detCutoff_testRestriction (φ : Test n) :
    ∃ (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ {x | x ≠ 0})
      (f : FullTest n), detCutoffTestCLM hχ hs f = φ := by
  obtain ⟨χ, hχ, hs, hone⟩ := exists_testDetCutoff φ
  let f : FullTest n := TestFunction.monoCLM ℝ φ
  have hf (A : Mat n) : f A = φ A := by
    change ((TestFunction.monoCLM ℝ φ : FullTest n) : (Mat n) → ℝ) A = _
    simp
  refine ⟨χ, hχ, hs, f, ?_⟩
  ext A
  rw [detCutoffTestCLM_apply, hf]
  by_cases hA : A ∈ tsupport φ
  · rw [hone A hA, mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hA, zero_mul]

/-- The full real matrix-space transpose theorem implies the theorem on
the open real units, by localization at the determinant of each test. -/
theorem realGeneralLinearTranspose_of_fullMatrixTranspose
    (h : ∀ (r : ℕ) (D : FullDistribution (r + 1)),
      IsFullConjugationInvariant D → IsFullTransposeInvariant D) :
    Langlands.RealGeneralLinearConjugationDistributionTransposeStatement := by
  intro r D hD φ
  obtain ⟨χ, hχ, hs, f, hf⟩ := exists_detCutoff_testRestriction φ
  have H := h r (extendDistributionByDetCutoff D hχ hs)
    (isFullConjugationInvariant_extendDistributionByDetCutoff D hD hχ hs) f
  change D (detCutoffTestCLM hχ hs (fullTransposeTest f)) = D (detCutoffTestCLM hχ hs f) at H
  rw [detCutoffTestCLM_fullTranspose, hf] at H
  exact H

end Langlands.HarmonicAnalysis.RealGeneralLinearDistribution
