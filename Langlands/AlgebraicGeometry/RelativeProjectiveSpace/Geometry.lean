import Langlands.AlgebraicGeometry.ProjectiveSpace.Charts
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.TwistOne
import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverProof
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Properness and affine coordinate charts of relative projective space -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

instance isProper_toBase (S : Scheme.{u}) (n : ℕ) : IsProper (toBase S n) := by
  have hp : IsProper (projectiveSpaceToSpec (ULift.{u} ℤ) n) := by
    rw [ProjectiveSpace.toSpec_eq_projSpace_π]
    infer_instance
  have he : terminal.from (ProjectiveSpace (ULift.{u} ℤ) n) =
      projectiveSpaceToSpec (ULift.{u} ℤ) n ≫
        (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).hom :=
    terminalIsTerminal.hom_ext _ _
  have : IsProper (terminal.from (ProjectiveSpace (ULift.{u} ℤ) n)) := by
    rw [he]
    infer_instance
  dsimp [toBase, RelativeProjectiveSpace]
  infer_instance

/-- Over an affine base the projection to integral projective space is affine. -/
instance isAffineHom_toIntegral (S : Scheme.{u}) [IsAffine S] (n : ℕ) :
    IsAffineHom (toIntegral S n) := by
  dsimp [toIntegral, RelativeProjectiveSpace]
  exact MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom (terminal.from S)))

/-- Every standard coordinate chart is affine over an affine base. -/
lemma isAffineOpen_coordinateOpen (S : Scheme.{u}) [IsAffine S] (n : ℕ)
    (i : Fin (n + 1)) : IsAffineOpen (coordinateOpen S n i) :=
  (isAffineOpen_projectiveSpaceCoordinateOpen (ULift.{u} ℤ) n i).preimage (toIntegral S n)

/-- The projection of a scheme-theoretic projective fibre to the integral model. -/
def fiberToIntegral (S : Scheme.{u}) (n : ℕ) (s : S) :
    (toBase S n).fiber s ⟶ ProjectiveSpace (ULift.{u} ℤ) n :=
  (toBase S n).fiberι s ≫ toIntegral S n

/-- The projection of a scheme-theoretic projective fibre to the integral model is affine. -/
instance isAffineHom_fiberToIntegral (S : Scheme.{u}) (n : ℕ) (s : S) :
    IsAffineHom (fiberToIntegral S n s) := by
  have h₁ : IsPullback ((toBase S n).fiberToSpecResidueField s)
      ((toBase S n).fiberι s) (S.fromSpecResidueField s) (toBase S n) :=
    (IsPullback.of_hasPullback _ _).flip
  have h₂ : IsPullback (toBase S n) (toIntegral S n) (terminal.from S)
      (terminal.from (ProjectiveSpace (ULift.{u} ℤ) n)) :=
    IsPullback.of_hasPullback _ _
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) (h₁.paste_vert h₂) inferInstance

/-- The inverse images of standard coordinate charts in every residue-field fibre are affine. -/
lemma isAffineOpen_fiber_coordinateOpen (S : Scheme.{u}) (n : ℕ) (s : S)
    (i : Fin (n + 1)) :
    IsAffineOpen ((toBase S n).fiberι s ⁻¹ᵁ coordinateOpen S n i) := by
  change IsAffineOpen ((toBase S n).fiberι s ⁻¹ᵁ
    ((toIntegral S n) ⁻¹ᵁ projectiveSpaceCoordinateOpen (ULift.{u} ℤ) n i))
  rw [← Scheme.Hom.comp_preimage]
  exact (isAffineOpen_projectiveSpaceCoordinateOpen (ULift.{u} ℤ) n i).preimage
    (fiberToIntegral S n s)

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace
