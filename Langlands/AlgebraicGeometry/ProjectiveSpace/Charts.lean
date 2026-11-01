import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverProof
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace

/-! # Connecting the published projective-space chart APIs

This internal adapter reuses the published FLT affine cover and identifies
its structure morphism and open ranges with the Library projective-space names.
The imported source port retains its attribution in `licenses/Anthropic-FLT/`.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The two published projective-space structure morphisms are definitionally equal. -/
theorem toSpec_eq_projSpace_π :
    projectiveSpaceToSpec R n = _root_.AlgebraicGeometry.ProjSpace.π R n := rfl

/-- The published FLT cover, viewed as a cover of the Library projective space. -/
abbrev affineOpenCover : (ProjectiveSpace R n).AffineOpenCover :=
  _root_.AlgebraicGeometry.ProjSpace.affineOpenCover R n

/-- Expose the published chart algebra at the Library grading wrapper. -/
instance algebraAway (j : Fin (n + 1)) :
    Algebra R (HomogeneousLocalization.Away (projectiveSpaceGrading R n) (MvPolynomial.X j)) :=
  _root_.AlgebraicGeometry.ProjSpace.algebraAway R n j

/-- Each chart is over the existing projective-space structure morphism. -/
theorem affineOpenCover_comp_toSpec (j : Fin (n + 1)) :
    (affineOpenCover R n).openCover.f j ≫ projectiveSpaceToSpec R n =
      Spec.map (CommRingCat.ofHom (algebraMap R
        (HomogeneousLocalization.Away (projectiveSpaceGrading R n) (MvPolynomial.X j)))) :=
  _root_.AlgebraicGeometry.ProjSpace.awayι_comp_π R n j

instance isOpenImmersion_affineOpenCover_f (j : Fin (n + 1)) :
    IsOpenImmersion ((affineOpenCover R n).openCover.f j) := by
  change IsOpenImmersion (Proj.awayι (projectiveSpaceGrading R n) (MvPolynomial.X j)
    (projectiveSpace_X_mem R n j) Nat.one_pos)
  infer_instance

/-- The ranges of the published cover are the Library coordinate opens. -/
theorem affineOpenCover_opensRange (j : Fin (n + 1)) :
    ((affineOpenCover R n).openCover.f j).opensRange =
      projectiveSpaceCoordinateOpen R n j :=
  Proj.opensRange_awayι (projectiveSpaceGrading R n) (MvPolynomial.X j)
    (projectiveSpace_X_mem R n j) Nat.one_pos

end Langlands.AlgebraicGeometry.ProjectiveSpace
