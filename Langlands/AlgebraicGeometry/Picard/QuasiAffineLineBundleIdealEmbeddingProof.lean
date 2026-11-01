import Langlands.AlgebraicGeometry.Picard.QuasiAffineLineBundleIdealEmbeddingStatement
import Langlands.AlgebraicGeometry.Picard.QuasiAffineLineBundleFiniteSectionProof
import Langlands.AlgebraicGeometry.Picard.LineBundleFiniteMonoDetector
import Langlands.AlgebraicGeometry.Picard.LineBundleDualSectionEvaluation

/-! # Embedding a line bundle into the structure module on a quasi-affine scheme -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Every line bundle on a locally Noetherian quasi-affine scheme embeds into
the structure module. -/
theorem quasiAffineLineBundleIdealEmbedding :
    QuasiAffineLineBundleIdealEmbeddingStatement.{u} := by
  intro X _ _ D
  obtain ⟨E, hE, hdet⟩ := D.property.exists_finite_mono_detector
  obtain ⟨t, ht⟩ := quasiAffineLineBundleFiniteSection X D.dual E hE
  refine ⟨D.evalSection t, hdet _ ?_⟩
  intro x hx
  exact D.isIso_stalk_evalSection_of_mem t (ht hx)

end Langlands.AlgebraicGeometry.Picard
