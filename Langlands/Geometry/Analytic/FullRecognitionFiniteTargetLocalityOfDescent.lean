import Langlands.Geometry.Analytic.FullRecognitionFiniteTargetRecognition
import Langlands.Geometry.Analytic.FullRecognitionFiniteTargetHausdorff
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.Statement

/-! # Assembly of the target-local finiteness criterion -/

noncomputable section

universe u v w

open scoped Topology

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- One strong map: finite target families and effective descent of the local
finite models of every family refinement give `g.IsFiniteOver V U`. -/
theorem isFiniteOver_of_effectiveRefinements
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (V : Set A.space) (U : Set B.space)
    (hVU : g.baseMap '' V ⊆ U) (hfam : g.HasFiniteTargetFamilies V U)
    (hreal : ∀ (W : B.atlas.saturatedAtlas.RecognizedSubset) (F : g.FamilyRefinement V U W),
      Nonempty (FiniteAffinoidAlgebraDescent.EffectiveRealization F.models.algebraDescentData)) :
    g.IsFiniteOver V U := by
  refine ⟨hVU, fun W hWU => ?_⟩
  let F := hfam.refinement W hWU
  have := g.t2Space_inter_preimage_locus_of_targetFamilies V U hfam W hWU
  let P := (hreal W F).some
  exact ⟨F.preimage P, F.preimage_admissible P, F.preimage_locus P,
    F.pullback_isFiniteBanach P⟩

set_option linter.defProp false in
/-- The target-local finiteness criterion, conditional on effective finite
Banach affinoid algebra descent. It is declared with `def` (its type is a
proposition) so that it can be recorded as a supporting definition artifact. -/
def finiteOverTargetLocality_of_descent
    (hdesc : FiniteAffinoidAlgebraDescentStatement.{u}) :
    FiniteOverTargetLocalityStatement.{u, v, w} K := by
  intro A B g V U _ _ hVU hfam
  exact g.isFiniteOver_of_effectiveRefinements V U hVU hfam
    (fun W F => hdesc K W.algebra F.models.rightCover.cover F.models.descentLocalAlgebras
      F.models.algebraDescentData)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
