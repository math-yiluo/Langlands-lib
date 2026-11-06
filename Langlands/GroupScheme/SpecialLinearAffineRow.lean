import Langlands.GroupScheme.SpecialLinearRowCoordinates
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.HomogeneousCharacterCoordinates
import Langlands.GroupScheme.Reductive.BinaryHomogeneousBasis

/-! # Row polynomials in the actual affine coordinates of the special linear group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SpecialLinear

section Coordinates

variable (n : Type) [Fintype n] [DecidableEq n] (k : Type u) [Field k]

local instance : IsAffine (groupScheme n (CommRingCat.of k)).X.left :=
  isAffine_groupScheme n (CommRingCat.of k)

/-- The determinant-one quotient is the chosen affine coordinate algebra of the group. -/
def coordinateAlgEquiv :
    CoordinateRing n k ≃ₐ[k] AffineCoordinates.algebra (groupScheme n (CommRingCat.of k)) :=
  (Corepresented.affineSectionsAlgEquiv (coordinateAlgebra n (CommRingCat.of k))).symm.trans
    (AffineCoordinates.globalAlgEquiv (groupScheme n (CommRingCat.of k))).symm

variable {n k}

/-- Under the coordinate comparison, evaluation is the relative spectrum adjunction map. -/
theorem pointAlgebraHom_coordinateAlgEquiv
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ (groupScheme n (CommRingCat.of k)).X)
    (b : CoordinateRing n k) :
    AffineCoordinates.pointAlgebraHom (groupScheme n (CommRingCat.of k)) T x
        (coordinateAlgEquiv n k b) =
      (((algΓAlgSpecAdjunction (CommRingCat.of k)).homEquiv T
        (op (coordinateAlgebra n (CommRingCat.of k)))).symm x).unop.hom b := by
  rw [AffineCoordinates.pointAlgebraHom_apply_eq, adjunction_homEquiv_symm_apply]
  apply congrArg x.left.appTop
  change (AffineCoordinates.globalAlgEquiv (groupScheme n (CommRingCat.of k)))
      ((AffineCoordinates.globalAlgEquiv (groupScheme n (CommRingCat.of k))).symm
        ((Corepresented.affineSectionsAlgEquiv
          (coordinateAlgebra n (CommRingCat.of k))).symm b)) = _
  exact (AlgEquiv.apply_symm_apply _ _).trans (by rfl)

/-- Row-polynomial functions as elements of the actual affine coordinate algebra. -/
def affineRowPolynomial (r : n) :
    MvPolynomial n k →ₐ[k] AffineCoordinates.algebra (groupScheme n (CommRingCat.of k)) :=
  (coordinateAlgEquiv n k).toAlgHom.comp (rowPolynomial r)

/-- Evaluation of an affine row polynomial on every relative test scheme. -/
theorem pointAlgebraHom_affineRowPolynomial
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ (groupScheme n (CommRingCat.of k)).X)
    (r : n) (f : MvPolynomial n k) :
    AffineCoordinates.pointAlgebraHom (groupScheme n (CommRingCat.of k)) T x
        (affineRowPolynomial (k := k) r f) =
      aeval (S₁ := ((algΓ (CommRingCat.of k)).obj T).unop)
        (fun j => pointsEquiv n (CommRingCat.of k) T x r j) f := by
  have h := AlgHom.congr_fun
    (comp_rowPolynomial
      (((algΓAlgSpecAdjunction (CommRingCat.of k)).homEquiv T
        (op (coordinateAlgebra n (CommRingCat.of k)))).symm x).unop.hom r) f
  exact (pointAlgebraHom_coordinateAlgEquiv T x _).trans h

/-- Homogeneous row polynomials in the actual affine coordinate algebra. -/
def affineHomogeneousRowMap (m : ℕ) (r : n) :
    homogeneousSubmodule n k m →ₗ[k]
      AffineCoordinates.algebra (groupScheme n (CommRingCat.of k)) :=
  (coordinateAlgEquiv n k).toLinearMap.comp (homogeneousRowMap m r)

@[simp] theorem affineHomogeneousRowMap_apply (m : ℕ) (r : n)
    (f : homogeneousSubmodule n k m) :
    affineHomogeneousRowMap m r f =
      affineRowPolynomial (k := k) r (f : MvPolynomial n k) := rfl

/-- The whole binary homogeneous space embeds into the actual affine coordinates. -/
theorem binaryAffineHomogeneousRowMap_injective (m : ℕ) :
    Function.Injective (affineHomogeneousRowMap (n := Fin 2) (k := k) m 1) :=
  (coordinateAlgEquiv (Fin 2) k).injective.comp (binaryHomogeneousRowMap_injective m)

end Coordinates

section BinaryCovariance

open HomogeneousPolynomial

variable {k : Type u} [Field k]

local instance : IsAffine (groupScheme (Fin 2) (CommRingCat.of k)).X.left :=
  isAffine_groupScheme (Fin 2) (CommRingCat.of k)

local instance : IsAffineHom (groupScheme (Fin 2) (CommRingCat.of k)).X.hom :=
  isAffineHom_groupScheme (Fin 2) (CommRingCat.of k)

/-- Evaluation of a homogeneous binary polynomial scales by its full degree over every
commutative test algebra, including nonreduced test algebras. -/
theorem aeval_binaryHomogeneous_scale {S : Type u} [CommRing S] [Algebra k S]
    (m : ℕ) (f : homogeneousSubmodule (Fin 2) k m) (t : S) (x : Fin 2 → S) :
    aeval (fun j => t * x j) (f : MvPolynomial (Fin 2) k) =
      t ^ m * aeval x (f : MvPolynomial (Fin 2) k) := by
  rw [eq_sum_binaryBasis m f]
  simp only [map_sum, map_mul, map_pow, aeval_C, aeval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc : c.val + (m - c.val) = m := Nat.add_sub_of_le (Nat.le_of_lt_succ c.isLt)
  have ht : t ^ m = t ^ c.val * t ^ (m - c.val) := by rw [← pow_add, hc]
  rw [mul_pow, mul_pow, ht]
  ring

/-- The bottom row of an upper-triangular matrix product is scaled by its last diagonal. -/
theorem upper_mul_bottomRow {S : Type u} [CommRing S]
    (a g : Matrix.SpecialLinearGroup (Fin 2) S) (ha : a 1 0 = 0) (j : Fin 2) :
    (a * g) 1 j = a 1 1 * g 1 j := by
  change ∑ l : Fin 2, a 1 l * g l j = _
  rw [Fin.sum_univ_two, ha, zero_mul, zero_add]

variable {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- An actual upper-triangular subgroup map and its last-diagonal coordinate make every
homogeneous bottom-row function covariant on the entire affine coordinate algebra. -/
theorem affineHomogeneousRowMap_mem_leftCovariant
    (i : H ⟶ groupScheme (Fin 2) (CommRingCat.of k))
    (χ : AffineCoordinates.algebra H)
    (hi : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X),
      pointsEquiv (Fin 2) (CommRingCat.of k) T (h ≫ i.hom.hom) 1 0 = 0)
    (hχ : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X),
      AffineCoordinates.pointAlgebraHom H T h χ =
        pointsEquiv (Fin 2) (CommRingCat.of k) T (h ≫ i.hom.hom) 1 1)
    (m : ℕ) (f : homogeneousSubmodule (Fin 2) k m) :
    affineHomogeneousRowMap m 1 f ∈ AffineCoordinates.leftCovariantSubspace i (χ ^ m) := by
  apply AffineCoordinates.mem_leftCovariantSubspace_of_points
  intro T h g
  have hrow :
      (fun j => pointsEquiv (Fin 2) (CommRingCat.of k) T ((h ≫ i.hom.hom) * g) 1 j) =
        (fun j => pointsEquiv (Fin 2) (CommRingCat.of k) T (h ≫ i.hom.hom) 1 1 *
          pointsEquiv (Fin 2) (CommRingCat.of k) T g 1 j) := by
    funext j
    rw [map_mul]
    exact upper_mul_bottomRow _ _ (hi T h) j
  change AffineCoordinates.pointAlgebraHom _ T _
      (affineRowPolynomial (k := k) 1 (f : MvPolynomial (Fin 2) k)) =
    _ * AffineCoordinates.pointAlgebraHom _ T _
      (affineRowPolynomial (k := k) 1 (f : MvPolynomial (Fin 2) k))
  rw [pointAlgebraHom_affineRowPolynomial, pointAlgebraHom_affineRowPolynomial,
    map_pow, hχ, hrow]
  exact aeval_binaryHomogeneous_scale m f _ _

end BinaryCovariance

end Langlands.GroupScheme.SpecialLinear
