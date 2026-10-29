import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateGenerationOpenStatement
import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneLocalFramesProof

/-! # Proof: the whole generation opens of the coordinate sections of `𝒪(1)` -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

universe u

/-- Every point of the generation open of the coordinate section `X i` of `𝒪(1)` lies in the
coordinate open `D₊(X i)`. -/
lemma trivializationOpen_twistOneCoordinate_le (R : Type u) [CommRing R] (n : ℕ)
    (i : Fin (n + 1)) :
    Langlands.SchemeModule.trivializationOpen (twistOne R n) (twistOneCoordinate R n i) ≤
      projectiveSpaceCoordinateOpen R n i := by
  intro x hx
  obtain ⟨V, hV, hxV⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
  have hcov : x ∈ ⨆ j : Fin (n + 1), projectiveSpaceCoordinateOpen R n j := by
    rw [iSup_projectiveSpaceCoordinateOpen R n]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  obtain ⟨g, hg⟩ :=
    ((Langlands.SchemeModule.LineBundleDescent.trivializesOn_iff_bijective _ _ V).mp hV V
      le_rfl).2 ((twistOne R n).presheaf.map (homOfLE le_top : V ⟶ ⊤).op
        (twistOneCoordinate R n j))
  rw [Langlands.SchemeModule.LineBundleDescent.sectionHom_app] at hg
  have e : (g.1 ⟨x, hxV⟩).val * Localization.mk (MvPolynomial.X i) 1 =
      Localization.mk (MvPolynomial.X j) 1 :=
    congrFun (congrArg Subtype.val hg) ⟨x, hxV⟩
  have hu : IsUnit (Localization.mk (MvPolynomial.X i) 1 :
      ProjTwist.Localizations (projectiveSpaceGrading R n) x) :=
    isUnit_of_mul_isUnit_right (e ▸ ProjTwist.isUnit_mk_one x hj)
  rw [Localization.mk_one_eq_algebraMap] at hu
  exact (IsLocalization.AtPrime.isUnit_to_map_iff
    (ProjTwist.Localizations (projectiveSpaceGrading R n) x) _ (MvPolynomial.X i)).mp hu

/-- The whole generation open of the coordinate section `X i` of `𝒪(1)` on projective space is
the coordinate open `D₊(X i)`. -/
theorem projectiveSpaceCoordinateGenerationOpen :
    ProjectiveSpaceCoordinateGenerationOpenStatement.{u} := by
  intro R _ n i
  refine le_antisymm (trivializationOpen_twistOneCoordinate_le R n i) ?_
  exact (Langlands.SchemeModule.maximalTrivialization _ _ _ _).mp
    ((projectiveSpaceTwistOneLocalFrames R n).1 i)

end Langlands.AlgebraicGeometry
