import Langlands.GroupScheme.Lie.AffineCoordinates
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Actual affine commutator pullbacks and their identity slices -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates

open Lie

variable {R : CommRingCat.{u}}

section Universal

variable (H : GroupScheme (Spec R)) [IsAffineHom H.X.hom]

/-- The actual affine point corresponding to the identity coordinate map. -/
def genericPoint : AffinePoints H (coordinateAlgebra H) :=
  (pointCoordinates H).symm (AlgHom.id R (coordinateAlgebra H))

@[simp] theorem genericPoint_coordinates :
    pointCoordinates H (genericPoint H) = AlgHom.id R (coordinateAlgebra H) :=
  (pointCoordinates H).apply_symm_apply _

/-- Every affine point is obtained from the generic point by its coordinate map. -/
theorem genericPoint_recover {A : Type u} [CommRing A] [Algebra R A]
    (x : AffinePoints H A) :
    affineMap H (pointCoordinates H x) (genericPoint H) = x := by
  apply (pointCoordinates H).injective
  rw [pointCoordinates_naturality, genericPoint_coordinates, AlgHom.comp_id]

@[simp] theorem genericPoint_origin :
    affineMap H (coordinateOrigin H) (genericPoint H) = 1 :=
  genericPoint_recover H 1

end Universal

section TensorPoints

variable (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
variable {A B C : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

/-- The commutator of two actual points after their independent tensor inclusions. -/
def tensorPoint (x : AffinePoints G A) (y : AffinePoints G B) :
    AffinePoints G (A ⊗[R] B) :=
  affineMap G Algebra.TensorProduct.includeLeft x *
    affineMap G Algebra.TensorProduct.includeRight y *
    (affineMap G Algebra.TensorProduct.includeLeft x)⁻¹ *
    (affineMap G Algebra.TensorProduct.includeRight y)⁻¹

/-- The algebra pullback of the commutator with independently variable inputs. -/
def tensorPullback (x : AffinePoints G A) (y : AffinePoints G B) :
    coordinateAlgebra G →ₐ[R] A ⊗[R] B :=
  pointCoordinates G (tensorPoint G x y)

/-- Evaluation of the tensor pullback is the actual commutator of evaluated points. -/
theorem tensorPullback_evaluate (x : AffinePoints G A) (y : AffinePoints G B)
    (φ : A ⊗[R] B →ₐ[R] C) :
    φ.comp (tensorPullback G x y) =
      pointCoordinates G
        (affineMap G (φ.comp Algebra.TensorProduct.includeLeft) x *
          affineMap G (φ.comp Algebra.TensorProduct.includeRight) y *
          (affineMap G (φ.comp Algebra.TensorProduct.includeLeft) x)⁻¹ *
          (affineMap G (φ.comp Algebra.TensorProduct.includeRight) y)⁻¹) := by
  rw [tensorPullback, ← pointCoordinates_naturality]
  simp only [tensorPoint, map_mul, map_inv, ← affineMap_comp]

/-- If the first evaluated point is the identity, the commutator pullback is constant. -/
theorem tensorPullback_constant_of_left
    (x : AffinePoints G A) (y : AffinePoints G B) (φ : A ⊗[R] B →ₐ[R] C)
    (hx : affineMap G (φ.comp Algebra.TensorProduct.includeLeft) x = 1) :
    φ.comp (tensorPullback G x y) =
      (Algebra.ofId R C).comp (coordinateOrigin G) := by
  rw [tensorPullback_evaluate, hx]
  simp only [one_mul, inv_one, mul_one, mul_inv_cancel, pointCoordinates_one]

/-- The second identity slice also gives the constant identity pullback. -/
theorem tensorPullback_constant_of_right
    (x : AffinePoints G A) (y : AffinePoints G B) (φ : A ⊗[R] B →ₐ[R] C)
    (hy : affineMap G (φ.comp Algebra.TensorProduct.includeRight) y = 1) :
    φ.comp (tensorPullback G x y) =
      (Algebra.ofId R C).comp (coordinateOrigin G) := by
  rw [tensorPullback_evaluate, hy]
  simp only [mul_one, mul_inv_cancel, inv_one, pointCoordinates_one]

/-- Specialize the first tensor factor to an augmentation which sends its point to 1. -/
theorem tensorPullback_left_identity_slice
    (x : AffinePoints G A) (y : AffinePoints G B)
    (εA : A →ₐ[R] R) (hx : affineMap G εA x = 1) :
    (Algebra.TensorProduct.lift ((Algebra.ofId R B).comp εA) (AlgHom.id R B)
      (fun _ _ => Commute.all _ _)).comp (tensorPullback G x y) =
      (Algebra.ofId R B).comp (coordinateOrigin G) := by
  apply tensorPullback_constant_of_left
  rw [Algebra.TensorProduct.lift_comp_includeLeft, affineMap_comp, hx, map_one]

/-- Specialize the second tensor factor to its identity augmentation. -/
theorem tensorPullback_right_identity_slice
    (x : AffinePoints G A) (y : AffinePoints G B)
    (εB : B →ₐ[R] R) (hy : affineMap G εB y = 1) :
    (Algebra.TensorProduct.lift (AlgHom.id R A) ((Algebra.ofId R A).comp εB)
      (fun _ _ => Commute.all _ _)).comp (tensorPullback G x y) =
      (Algebra.ofId R A).comp (coordinateOrigin G) := by
  apply tensorPullback_constant_of_right
  rw [Algebra.TensorProduct.lift_comp_includeRight', affineMap_comp, hy, map_one]

end TensorPoints

section Subgroups

variable {G H K : GroupScheme (Spec R)}

/-- The actual scheme commutator morphism for two homomorphisms into G. -/
def commutatorHom (i : H ⟶ G) (j : K ⟶ G) : H.X ⊗ K.X ⟶ G.X :=
  (fst H.X K.X ≫ i.hom.hom) * (snd H.X K.X ≫ j.hom.hom) *
    (fst H.X K.X ≫ i.hom.hom)⁻¹ * (snd H.X K.X ≫ j.hom.hom)⁻¹

/-- Every test of the commutator morphism is the commutator of its two inputs. -/
theorem commutatorHom_apply (i : H ⟶ G) (j : K ⟶ G)
    {T : Over (Spec R)} (x : T ⟶ H.X) (y : T ⟶ K.X) :
    lift x y ≫ commutatorHom i j =
      (x ≫ i.hom.hom) * (y ≫ j.hom.hom) *
        (x ≫ i.hom.hom)⁻¹ * (y ≫ j.hom.hom)⁻¹ := by
  simp only [commutatorHom, MonObj.comp_mul, GrpObj.comp_inv,
    lift_fst_assoc, lift_snd_assoc]

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom K.X.hom]

/-- Coordinate pullback of the actual commutator, with both subgroup inputs universal. -/
def pullback (i : H ⟶ G) (j : K ⟶ G) :
    coordinateAlgebra G →ₐ[R] coordinateAlgebra H ⊗[R] coordinateAlgebra K :=
  tensorPullback G (genericPoint H ≫ i.hom.hom) (genericPoint K ≫ j.hom.hom)

/-- The tensor-coordinate definition evaluates the actual scheme commutator morphism. -/
theorem pullback_is_commutator (i : H ⟶ G) (j : K ⟶ G) :
    pullback i j = pointCoordinates G
      (lift (affineMap H Algebra.TensorProduct.includeLeft (genericPoint H))
        (affineMap K Algebra.TensorProduct.includeRight (genericPoint K)) ≫
          commutatorHom i j) := by
  rw [commutatorHom_apply]
  simp only [pullback, tensorPullback, tensorPoint, affineMap_apply, Category.assoc]

omit [IsAffineHom G.X.hom] in
theorem image_genericPoint_origin (i : H ⟶ G) :
    affineMap G (coordinateOrigin H) (genericPoint H ≫ i.hom.hom) = 1 := by
  change (affineMap H (coordinateOrigin H) (genericPoint H)) ≫ i.hom.hom = 1
  rw [genericPoint_origin, MonObj.one_comp]

/-- The actual first identity slice has the constant identity pullback. -/
theorem pullback_left_identity_slice (i : H ⟶ G) (j : K ⟶ G) :
    (Algebra.TensorProduct.lift
      ((Algebra.ofId R (coordinateAlgebra K)).comp (coordinateOrigin H))
      (AlgHom.id R (coordinateAlgebra K)) (fun _ _ => Commute.all _ _)).comp
        (pullback i j) =
      (Algebra.ofId R (coordinateAlgebra K)).comp (coordinateOrigin G) :=
  tensorPullback_left_identity_slice G _ _ _ (image_genericPoint_origin i)

/-- The actual second identity slice has the constant identity pullback. -/
theorem pullback_right_identity_slice (i : H ⟶ G) (j : K ⟶ G) :
    (Algebra.TensorProduct.lift (AlgHom.id R (coordinateAlgebra H))
      ((Algebra.ofId R (coordinateAlgebra H)).comp (coordinateOrigin K))
      (fun _ _ => Commute.all _ _)).comp (pullback i j) =
      (Algebra.ofId R (coordinateAlgebra H)).comp (coordinateOrigin G) :=
  tensorPullback_right_identity_slice G _ _ _ (image_genericPoint_origin j)

end Subgroups

end Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates
