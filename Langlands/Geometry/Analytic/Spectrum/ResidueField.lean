import Langlands.Geometry.Analytic.Spectrum.ResidueField.Statement

/-! # Completed residue fields realize actual spectrum points -/

noncomputable section

universe u v

namespace Langlands.Analytic
namespace BanachSpectrum

variable {A : Type u} [NormedCommRing A]
  (K : Type v) [NormedField K] [IsUltrametricDist K] [NormedAlgebra K A]

@[simp]
theorem norm_completedResidueMap (x : BanachSpectrum A) (a : A) :
    ‖completedResidueMap K x a‖ = x a :=
  (UniformSpace.Completion.norm_coe (residueFieldMap K x a)).trans
    (norm_residueFieldMap K x a)

theorem completedResidueMap_eq_zero (x : BanachSpectrum A) (a : A) :
    completedResidueMap K x a = 0 ↔ a ∈ x.kernel := by
  rw [← norm_eq_zero, norm_completedResidueMap]
  rfl

/-- Every spectrum point is realized by the norm in its constructed
completed residue field. -/
theorem comap_completedResidueMap (x : BanachSpectrum A) :
    comap (completedResidueMap K x).toBoundedRingHom
      (fieldPoint (CompletedResidueField K x)) = x :=
  ext fun a => norm_completedResidueMap K x a

theorem isometry_residueCompletionMap (x : BanachSpectrum A) :
    Isometry (residueCompletionMap K x) :=
  UniformSpace.Completion.coe_isometry

theorem denseRange_residueCompletionMap (x : BanachSpectrum A) :
    DenseRange (residueCompletionMap K x) :=
  UniformSpace.Completion.denseRange_coe

end BanachSpectrum

/-- Norm evaluation, kernel identification and dense isometric inclusion for
the actual completed residue field. -/
theorem completedResidueFieldProperties : CompletedResidueFieldStatement.{u, v} := by
  intro A K _ _ _ _ x
  exact ⟨BanachSpectrum.norm_completedResidueMap K x,
    BanachSpectrum.completedResidueMap_eq_zero K x,
    BanachSpectrum.comap_completedResidueMap K x,
    BanachSpectrum.isometry_residueCompletionMap K x,
    BanachSpectrum.denseRange_residueCompletionMap K x⟩

end Langlands.Analytic
