import Langlands.GroupScheme.Rational.AffineCommutatorCoordinates
import Langlands.GroupScheme.AutomorphicAction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The actual affine commutator image -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates

open Lie

variable {R : CommRingCat.{u}} {G H K : GroupScheme (Spec R)}

/-- Equivariance of the actual two-input commutator under compatible automorphisms. -/
theorem commutatorHom_equivariant {S : GroupScheme (Spec R)}
    (b : AutomorphicAction S G) (c : AutomorphicAction S H)
    (d : AutomorphicAction S K) (i : H ⟶ G) (j : K ⟶ G)
    (hi : ∀ {T : Over (Spec R)} (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ i.hom.hom = b.act s (h ≫ i.hom.hom))
    (hj : ∀ {T : Over (Spec R)} (s : T ⟶ S.X) (h : T ⟶ K.X),
      d.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom))
    {T : Over (Spec R)} (s : T ⟶ S.X) (h : T ⟶ H.X) (h' : T ⟶ K.X) :
    lift (c.act s h) (d.act s h') ≫ commutatorHom i j =
      b.act s (lift h h' ≫ commutatorHom i j) := by
  simp only [commutatorHom_apply, hi, hj, b.act_mul_right, b.act_inv]

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom K.X.hom]

/-- The tensor coordinates present the actual product of the two input schemes. -/
def tensorPresentation :
    (algSpec R).obj (op (CommAlgCat.of R
      (coordinateAlgebra H ⊗[R] coordinateAlgebra K))) ≅ H.X ⊗ K.X :=
  prodComparisonIso (algSpec R) (op (coordinateAlgebra H)) (op (coordinateAlgebra K)) ≪≫
    (coordinateIso H ⊗ᵢ coordinateIso K)

theorem genericPoint_eq_coordinateIso :
    genericPoint H = (coordinateIso H).hom := by
  simp [genericPoint, pointCoordinates]

/-- The product presentation sends the independent universal points to the inputs. -/
theorem tensorPresentation_hom :
    (tensorPresentation (H := H) (K := K)).hom =
      lift (affineMap H Algebra.TensorProduct.includeLeft (genericPoint H))
        (affineMap K Algebra.TensorProduct.includeRight (genericPoint K)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [tensorPresentation, Iso.trans_hom, tensorIso_hom, lift_fst,
      affineMap_apply, genericPoint_eq_coordinateIso]
    rw [Category.assoc, tensorHom_fst, ← Category.assoc, prodComparisonIso_hom,
      prodComparison_fst]
    rfl
  · simp only [tensorPresentation, Iso.trans_hom, tensorIso_hom, lift_snd,
      affineMap_apply, genericPoint_eq_coordinateIso]
    rw [Category.assoc, tensorHom_snd, ← Category.assoc, prodComparisonIso_hom,
      prodComparison_snd]
    rfl

/-- The actual coordinate algebra of the affine commutator image. -/
def imageAlgebra (i : H ⟶ G) (j : K ⟶ G) :
    Subalgebra R (coordinateAlgebra H ⊗[R] coordinateAlgebra K) :=
  (pullback i j).range

/-- The coordinate quotient defining the closed affine image. -/
def imageQuotient (i : H ⟶ G) (j : K ⟶ G) :
    coordinateAlgebra G →ₐ[R] imageAlgebra i j :=
  (pullback i j).rangeRestrict

theorem imageQuotient_surjective (i : H ⟶ G) (j : K ⟶ G) :
    Function.Surjective (imageQuotient i j) :=
  (pullback i j).rangeRestrict_surjective

/-- Image coordinates embed into the independent input coordinates. -/
theorem imageAlgebra_injective (i : H ⟶ G) (j : K ⟶ G) :
    Function.Injective (Subalgebra.val (imageAlgebra i j)) :=
  Subtype.val_injective

/-- The actual affine image as a scheme over the original base. -/
def imageScheme (i : H ⟶ G) (j : K ⟶ G) : Over (Spec R) :=
  (algSpec R).obj (op (CommAlgCat.of R (imageAlgebra i j)))

/-- The closed-image morphism to G in its existing affine coordinates. -/
def imageInclusion (i : H ⟶ G) (j : K ⟶ G) : imageScheme i j ⟶ G.X :=
  (algSpec R).map (CommAlgCat.ofHom (imageQuotient i j)).op ≫ (coordinateIso G).hom

theorem imageInclusion_closed (i : H ⟶ G) (j : K ⟶ G) :
    IsClosedImmersion (imageInclusion i j).left := by
  let : IsIso (coordinateIso G).hom.left :=
    (Over.forget (Spec R)).map_isIso (coordinateIso G).hom
  let : IsClosedImmersion
      ((algSpec R).map (CommAlgCat.ofHom (imageQuotient i j)).op).left :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (imageQuotient i j).toRingHom) (imageQuotient_surjective i j)
  change IsClosedImmersion
    (((algSpec R).map (CommAlgCat.ofHom (imageQuotient i j)).op).left ≫
      (coordinateIso G).hom.left)
  infer_instance

/-- The tensor-coordinate test maps naturally to the closed image. -/
def imageProjection (i : H ⟶ G) (j : K ⟶ G) :
    (algSpec R).obj (op (CommAlgCat.of R
      (coordinateAlgebra H ⊗[R] coordinateAlgebra K))) ⟶ imageScheme i j :=
  (algSpec R).map (CommAlgCat.ofHom (Subalgebra.val (imageAlgebra i j))).op

theorem imageProjection_comp (i : H ⟶ G) (j : K ⟶ G) :
    imageProjection i j ≫ imageInclusion i j =
      (tensorPresentation (H := H) (K := K)).hom ≫ commutatorHom i j := by
  apply (pointCoordinates G).injective
  have he :
      pointCoordinates G (imageProjection i j ≫ imageInclusion i j) = pullback i j := by
    change pointCoordinates G
      (affineMap G (Subalgebra.val (imageAlgebra i j))
        ((pointCoordinates G).symm (imageQuotient i j))) = _
    rw [pointCoordinates_naturality, Equiv.apply_symm_apply]
    rfl
  rw [he, tensorPresentation_hom, ← pullback_is_commutator]

/-- The actual commutator morphism factors through the closed affine image. -/
def imageFactor (i : H ⟶ G) (j : K ⟶ G) : H.X ⊗ K.X ⟶ imageScheme i j :=
  (tensorPresentation (H := H) (K := K)).inv ≫ imageProjection i j

theorem imageFactor_comp (i : H ⟶ G) (j : K ⟶ G) :
    imageFactor i j ≫ imageInclusion i j = commutatorHom i j := by
  rw [imageFactor, Category.assoc, imageProjection_comp, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Every test-scheme commutator lies in the actual closed image. -/
theorem imageFactor_apply (i : H ⟶ G) (j : K ⟶ G)
    {T : Over (Spec R)} (h : T ⟶ H.X) (h' : T ⟶ K.X) :
    (lift h h' ≫ imageFactor i j) ≫ imageInclusion i j =
      (h ≫ i.hom.hom) * (h' ≫ j.hom.hom) *
        (h ≫ i.hom.hom)⁻¹ * (h' ≫ j.hom.hom)⁻¹ := by
  rw [Category.assoc, imageFactor_comp, commutatorHom_apply]

end Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates
