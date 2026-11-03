import Langlands.GroupScheme.Rational.AffineCommutatorImage
import Langlands.GroupScheme.Rational.PointedCoordinateAction

/-! # Coordinate injectivity of the actual affine commutator image -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates

variable {k : Type u} [Field k]

private def coordinatesOfPresentation {V : Over (Spec (CommRingCat.of k))}
    [IsAffineHom V.hom] {C : CommAlgCat (CommRingCat.of k)}
    (e : (algSpec (CommRingCat.of k)).obj (op C) ≅ V) : PointedCoordinateWeights.Coord V ≃ₐ[k] C :=
  CommAlgCat.algEquivOfIso
    (algSpec.fullyFaithful.preimageIso (e ≪≫ (PointedCoordinateWeights.coordinateIso V).symm)).unop

private theorem coordinatesOfPresentation_eq
    {V : Over (Spec (CommRingCat.of k))} [IsAffineHom V.hom]
    {C : CommAlgCat (CommRingCat.of k)}
    (e : (algSpec (CommRingCat.of k)).obj (op C) ≅ V) :
    (coordinatesOfPresentation e).toAlgHom = PointedCoordinateWeights.pointCoordinates e.hom := rfl

variable {G H K : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom K.X.hom]

instance imageScheme_isAffineHom (i : H ⟶ G) (j : K ⟶ G) :
    IsAffineHom (imageScheme i j).hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom
    (algebraMap (CommRingCat.of k) (imageAlgebra i j))))
  infer_instance

private instance input_isAffineHom : IsAffineHom (H.X ⊗ K.X).hom := by
  change IsAffineHom (pullback.fst H.X.hom K.X.hom ≫ H.X.hom)
  let : IsAffineHom (pullback.fst H.X.hom K.X.hom) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  infer_instance

/-- The chosen affine coordinates of the actual closed image are its explicit
range algebra, up to an actual algebra equivalence. -/
def imageCoordinates (i : H ⟶ G) (j : K ⟶ G) :
    PointedCoordinateWeights.Coord (imageScheme i j) ≃ₐ[k] imageAlgebra i j :=
  coordinatesOfPresentation (Iso.refl (imageScheme i j))

/-- The product presentation identifies chosen product coordinates with the
independent tensor coordinates used to define the commutator image. -/
def inputCoordinates :
    PointedCoordinateWeights.Coord (H.X ⊗ K.X) ≃ₐ[k]
      Lie.coordinateAlgebra H ⊗[CommRingCat.of k] Lie.coordinateAlgebra K :=
  coordinatesOfPresentation (tensorPresentation (H := H) (K := K))

/-- In explicit affine presentations, the image-factor pullback is exactly the
inclusion of the actual range algebra. -/
theorem imageFactor_pullback_coordinates (i : H ⟶ G) (j : K ⟶ G) :
    (inputCoordinates (H := H) (K := K)).toAlgHom.comp (PointedCoordinateWeights.pullback (imageFactor i j)) =
      (Subalgebra.val (imageAlgebra i j)).comp (imageCoordinates i j).toAlgHom := by
  rw [inputCoordinates, coordinatesOfPresentation_eq, ← PointedCoordinateWeights.coordinates_comp]
  have he : (tensorPresentation (H := H) (K := K)).hom ≫ imageFactor i j =
      imageProjection i j := by
    simp [imageFactor]
  rw [he]
  change PointedCoordinateWeights.pointCoordinates
      (PointedCoordinateWeights.pointsMap (Subalgebra.val (imageAlgebra i j)) (𝟙 (imageScheme i j))) = _
  rw [PointedCoordinateWeights.pointCoordinates_naturality]
  rfl

/-- Pullback from the actual closed commutator image is injective, without a
reducedness or smoothness assumption. -/
theorem imageFactor_pullback_injective (i : H ⟶ G) (j : K ⟶ G) :
    Function.Injective (PointedCoordinateWeights.pullback (imageFactor i j)) := by
  intro x y hxy
  apply (imageCoordinates i j).injective
  apply imageAlgebra_injective i j
  have hh := congrArg (inputCoordinates (H := H) (K := K)) hxy
  have hx := DFunLike.congr_fun (imageFactor_pullback_coordinates i j) x
  have hy := DFunLike.congr_fun (imageFactor_pullback_coordinates i j) y
  exact hx.symm.trans (hh.trans hy)

end Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates
