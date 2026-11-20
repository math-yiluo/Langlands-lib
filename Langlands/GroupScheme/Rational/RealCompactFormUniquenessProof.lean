import Langlands.GroupScheme.Rational.RealCompactFormDescent
import Langlands.GroupScheme.Rational.RealCompactFormMatrixConjugacy
import Langlands.GroupScheme.Rational.RealCompactFormUniquenessStatement
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Uniqueness of compact real semisimple forms -/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open GaloisPointComparison

/-- Compact real semisimple group schemes with isomorphic complexifications
are isomorphic over ℝ. -/
theorem realCompactFormUniqueness : RealCompactFormUniquenessStatement := by
  intro G₁ G₂ h₁ h₂ hc₁ hc₂ he
  obtain ⟨e⟩ := he
  have hr₁ := h₁.isConnectedReductive
  have hr₂ := h₂.isConnectedReductive
  let e' : baseChanged ℝ ℂ G₂ ≅ baseChanged ℝ ℂ G₁ := e.symm
  obtain ⟨N, ρ, hρ, hconj⟩ :=
    RealCompactFormUniqueness.exists_closed_representation_with_real_conjugator
      hr₁ hr₂ hc₁ hc₂ e'
  let : IsAlgClosure ℝ ℂ := ⟨inferInstance, Algebra.IsAlgebraic.of_finite ℝ ℂ⟩
  let : IsGalois ℝ ℂ := IsAlgClosure.isGalois ℝ ℂ
  obtain ⟨f⟩ := RealCompactForm.exists_iso_of_matrix_conjugator
    (k := ℝ) (L := ℂ) (G := G₁) (H := G₂) (n := Fin N) hr₁ hr₂ e' ρ hρ hconj
  exact ⟨f.symm⟩

end Langlands.GroupScheme
