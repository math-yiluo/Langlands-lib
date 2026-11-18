import Langlands.GroupScheme.AffineQuotientReduction
import Langlands.AlgebraicGeometry.ImmersionNilpotentReflection
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.NilpotentDiagonalizableDeformation

/-! # Affineness and diagonalizability from a nilpotent reduction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.NilpotentReduction

/-- Affineness of an affine-base nilpotent reduction implies affineness of the scheme. -/
theorem isAffine_of_baseChange {A : Type u} [CommRing A] (J : Ideal A)
    (hJ : IsNilpotent J) (X : Over (Spec (CommRingCat.of A)))
    [IsAffine ((Over.pullback (Spec.algebraMap A (A ⧸ J))).obj X).left] :
    IsAffine X.left := by
  let r := Spec.algebraMap A (A ⧸ J)
  have : IsClosedImmersion r :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : Surjective r :=
    Langlands.AlgebraicGeometry.Picard.InfinitesimalTensorNilpotence.spec_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      (by simpa only [Ideal.mk_ker] using hJ)
  let V : Over (Spec (CommRingCat.of A)) :=
    Over.mk (pullback.fst X.hom r ≫ X.hom)
  have : IsAffine V.left :=
    inferInstanceAs (IsAffine ((Over.pullback r).obj X).left)
  exact AffineQuotient.isAffine_of_finite_surjective
    (V := V) (Over.homMk (pullback.fst X.hom r) rfl)
    (inferInstanceAs (IsFinite (pullback.fst X.hom r)))
    (inferInstanceAs (Surjective (pullback.fst X.hom r)))

/-- The canonical affine presentation recovered from an affine nilpotent reduction. -/
def affinePresentation {A : Type u} [CommRing A] (J : Ideal A)
    (hJ : IsNilpotent J) (X : Over (Spec (CommRingCat.of A)))
    [IsAffine ((Over.pullback (Spec.algebraMap A (A ⧸ J))).obj X).left] :
    X.left ≅ Spec Γ(X.left, ⊤) := by
  have := isAffine_of_baseChange J hJ X
  exact X.left.isoSpec

/-- A group with multiplicative-type nilpotent reduction is affine over its base. -/
theorem isAffineHom_of_isMultiplicativeType {A : Type u} [CommRing A]
    (J : Ideal A) (hJ : IsNilpotent J)
    (H : GroupScheme (Spec (CommRingCat.of A)))
    (hH : RelativeMultiplicativeType.IsMultiplicativeType
      ((GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).obj H)) :
    IsAffineHom H.X.hom := by
  have := hH.isAffineHom
  have : IsAffine ((Over.pullback (Spec.algebraMap A (A ⧸ J))).obj H.X).left :=
    isAffine_of_isAffineHom
      ((GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).obj H).X.hom
  have := isAffine_of_baseChange J hJ H.X
  infer_instance

/-- The flat split reflection theorem needs no affineness assumption on the group. -/
theorem isDiagonalizable_of_baseChange {A : Type u} [CommRing A]
    (J : Ideal A) (hJ : IsNilpotent J)
    (H : GroupScheme (Spec (CommRingCat.of A))) [Flat H.X.hom]
    (hH : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).obj H)) :
    RelativeMultiplicativeType.IsDiagonalizable H := by
  have := isAffineHom_of_isMultiplicativeType J hJ H
    (RelativeMultiplicativeType.IsMultiplicativeType.of_isDiagonalizable hH)
  have := isAffine_of_isAffineHom H.X.hom
  exact CompleteLocalDeformation.isDiagonalizable_of_nilpotent_reduction H J hJ hH

end Langlands.GroupScheme.NilpotentReduction
