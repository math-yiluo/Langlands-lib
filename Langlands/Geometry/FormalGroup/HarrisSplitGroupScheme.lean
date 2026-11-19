import Langlands.Geometry.FormalGroup.HarrisSplitSimilitudes
import Langlands.GroupScheme.FiniteAlgebraRightRegular
import Langlands.GroupScheme.Products
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.SmoothProducts
import Mathlib.LinearAlgebra.TensorProduct.Opposite

/-! # The split algebraic similitude group in Harris's component factor -/

noncomputable section
universe u

namespace Langlands.FormalGroup.Harris

open _root_.AlgebraicGeometry CategoryTheory Opposite MulOpposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj TensorProduct

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {n : ℕ} (b : Module.Basis (Fin n) k Bᵐᵒᵖ)

/-- The split similitude group in its opposite-unit and multiplier coordinates. -/
abbrev splitGroupScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  FiniteAlgebraUnits.groupScheme b ⊗ (Gm (Spec (CommRingCat.of k))).toGrp

instance splitGroupScheme_isAffine : IsAffine (splitGroupScheme b).X.left := by
  change IsAffine (Limits.pullback (FiniteAlgebraUnits.groupScheme b).X.hom
    (Gm (Spec (CommRingCat.of k))).X.hom)
  infer_instance

instance splitGroupScheme_smooth : Smooth (splitGroupScheme b).X.hom :=
  smooth_tensor _ _ inferInstance (smooth_gm _)

/-- Actual points of the split algebraic group over every test scheme, with
coordinates in the units of the scalar-extended opposite algebra and of the base. -/
def splitGroupPointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (splitGroupScheme b).X) ≃*
      (((algΓ (CommRingCat.of k)).obj T).unop ⊗[k] Bᵐᵒᵖ)ˣ × (Γ(T.left, ⊤))ˣ :=
  (productPointsEquiv _ _ T).trans
    ((FiniteAlgebraUnits.pointsEquiv b T).prodCongr (Gm.pointsEquiv _ T))

/-- Scalar extension of the opposite algebra gives the actual split involutive algebra
of the test scheme's relative sections. -/
def splitGroupPointsSimilitudes (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (splitGroupScheme b).X) ≃*
      (splitInvolution ((algΓ (CommRingCat.of k)).obj T).unop
        (((algΓ (CommRingCat.of k)).obj T).unop ⊗[k] B)).similitudes := by
  let R := ((algΓ (CommRingCat.of k)).obj T).unop
  let e : R ⊗[k] Bᵐᵒᵖ ≃ₐ[k] (R ⊗[k] B)ᵐᵒᵖ :=
    (Algebra.TensorProduct.congr (AlgEquiv.toOpposite k R) (AlgEquiv.refl : Bᵐᵒᵖ ≃ₐ[k] Bᵐᵒᵖ)).trans
      (Algebra.TensorProduct.opAlgEquiv k k R B)
  exact (splitGroupPointsEquiv b T).trans
    (((Units.mapEquiv e.toMulEquiv).prodCongr (MulEquiv.refl _)).trans
      (splitSimilitudeCoordinates R (R ⊗[k] B)).symm)

/-- The point coordinates commute with actual test-scheme pullback. -/
theorem splitGroupPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ (splitGroupScheme b).X) :
    splitGroupPointsEquiv b T' (a ≫ x) =
      (Units.map (Algebra.TensorProduct.map (((algΓ (CommRingCat.of k)).map a).unop.hom)
        (AlgHom.id k Bᵐᵒᵖ)).toMonoidHom (splitGroupPointsEquiv b T x).1,
        Units.map a.left.appTop.hom.toMonoidHom (splitGroupPointsEquiv b T x).2) := by
  apply Prod.ext
  · change FiniteAlgebraUnits.pointsEquiv b T' ((a ≫ x) ≫ fst _ _) = _
    rw [Category.assoc, FiniteAlgebraUnits.pointsEquiv_naturality]
    rfl
  · change Gm.pointsEquiv _ T' ((a ≫ x) ≫ snd _ _) = _
    rw [Category.assoc, Gm.pointsEquiv_naturality]
    rfl

/-- The k-points are the original actual split similitude pairs. -/
def splitGroupRationalPointsEquiv : rationalPoints (splitGroupScheme b) ≃*
    (splitInvolution k B).similitudes :=
  (productPointsEquiv _ _ _).trans
    (((FiniteAlgebraUnits.rationalPointsEquiv b).prodCongr (Gm.affinePointsEquiv (𝟙 _))).trans
      (splitSimilitudeCoordinates k B).symm)

/-- The scalar multiplier is the second projection as an actual rational character. -/
def splitMultiplierCharacter : rationalCharacters (splitGroupScheme b) :=
  Additive.ofMul (snd _ _)

theorem characterEval_splitMultiplier (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (splitGroupScheme b).X) :
    characterEval (splitMultiplierCharacter b) T x = (splitGroupPointsEquiv b T x).2 := rfl

theorem rationalCharacterEval_splitMultiplier (x : rationalPoints (splitGroupScheme b)) :
    rationalCharacterEval (splitMultiplierCharacter b) x =
      (splitInvolution k B).multiplier (splitGroupRationalPointsEquiv b x) := by
  rw [← splitSimilitudeCoordinates_snd, splitGroupRationalPointsEquiv,
    MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

/-- The determinant of the right regular representation of the opposite unit factor
is an actual rational character. -/
def splitRegularDeterminantCharacter : rationalCharacters (splitGroupScheme b) :=
  characterRestrict (fst _ _ ≫ FiniteAlgebraUnits.rightRegularRepresentation b)
    (GeneralLinear.determinantCharacter (Fin n) (CommRingCat.of k))

theorem characterEval_splitRegularDeterminant (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (splitGroupScheme b).X) :
    characterEval (splitRegularDeterminantCharacter b) T x =
      Matrix.GeneralLinearGroup.det (FiniteAlgebraUnits.rightRegularUnits b
        ((algΓ (CommRingCat.of k)).obj T).unop (splitGroupPointsEquiv b T x).1) := by
  rw [splitRegularDeterminantCharacter, characterEval_characterRestrict,
    GeneralLinear.characterEval_determinantCharacter]
  change Matrix.GeneralLinearGroup.det (GeneralLinear.pointsEquiv _ _ T
    ((x ≫ fst _ _) ≫ (FiniteAlgebraUnits.rightRegularRepresentation b).hom.hom)) = _
  rw [FiniteAlgebraUnits.pointsEquiv_rightRegularRepresentation]
  rfl

end Langlands.FormalGroup.Harris
