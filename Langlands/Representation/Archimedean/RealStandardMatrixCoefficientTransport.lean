import Langlands.Representation.Archimedean.RealReverseTransfer

/-! # Transport of real standard module matrix coefficients

An intertwiner carries compatible compact integral functionals to equal matrix
coefficients throughout the group. See the paired Markdown.
-/

noncomputable section
open scoped TensorProduct
set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean MeasureTheory

/-- If two continuous compact integral tests agree along a standard intertwiner at the
identity, their matrix coefficients agree for every group element. -/
def RealStandardMatrixCoefficientTransportStatement : Prop :=
  ∀ (n : ℕ) (ds es : List RealBlock)
    (T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)),
    IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T →
      ∀ (μ : Measure (Matrix.unitaryGroup (Fin n) ℝ)) [IsFiniteMeasure μ]
        (φ ψ : Matrix.unitaryGroup (Fin n) ℝ → ℂ),
        Continuous φ → Continuous ψ →
          (∀ v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
            MatrixCoefficientAnalytic.matrixCoefficient μ v φ 1 =
              MatrixCoefficientAnalytic.matrixCoefficient μ (T v) ψ 1) →
            ∀ (v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
              (g : Langlands.GeneralLinear n ℝ),
              MatrixCoefficientAnalytic.matrixCoefficient μ v φ g =
                MatrixCoefficientAnalytic.matrixCoefficient μ (T v) ψ g

theorem realStandardMatrixCoefficientTransport :
    RealStandardMatrixCoefficientTransportStatement := by
  intro n ds es T hT μ hμ φ ψ hφ hψ h1 v g
  let P (a b : Langlands.GeneralLinear n ℝ → ℂ) : Prop :=
    ∃ w : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
      a = (w : Langlands.GeneralLinear n ℝ → ℂ) ∧
      b = (T w : Langlands.GeneralLinear n ℝ → ℂ)
  refine RealReverseTransfer.matrixCoefficient_eq_of_rel μ
    (GramFormula.realPositionExponent ds) (GramFormula.realPositionExponent es)
    (GramFormula.realPositionCharacter_eq_signUnit_mul ds)
    (GramFormula.realPositionCharacter_eq_signUnit_mul es) P ?_ ?_ ?_ hφ hψ ?_
    v (T v) ⟨v, rfl, rfl⟩ g
  · rintro a b ⟨w, rfl, rfl⟩
    exact ⟨RealReverseTransfer.mem_kFiniteFunctions_principalSeries w.2,
      RealReverseTransfer.mem_kFiniteFunctions_principalSeries (T w).2⟩
  · rintro k hk a b ⟨w, rfl, rfl⟩
    refine ⟨realStandardRep n ds ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ w, ?_, ?_⟩
    · rw [realStandardRep_apply_coe, RealReverseTransfer.toUnits_mk]
    · rw [hT.map_realStandardRep, realStandardRep_apply_coe, RealReverseTransfer.toUnits_mk]
  · rintro X a b ⟨w, rfl, rfl⟩
    refine ⟨realStandardLie n ds (1 ⊗ₜ X) w, ?_, ?_⟩
    · rw [realStandardLie_one_tmul_apply_coe]
    · rw [hT.map_realStandardLie, realStandardLie_one_tmul_apply_coe]
  · rintro a b ⟨w, rfl, rfl⟩
    exact h1 w

end Langlands.Archimedean
