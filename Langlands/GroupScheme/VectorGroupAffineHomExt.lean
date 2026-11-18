import Langlands.GroupScheme.AffinePointComparison
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Affine coordinates detect homomorphisms to vector groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.VectorGroup

variable {R : CommRingCat.{u}} {n : ℕ}
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]

/-- The additive coordinates of a vector-group point over an affine test algebra. -/
def affineCoordinates (A : CommAlgCat.{u} R)
    (x : (groupScheme R n).affinePoints A) : Fin n → A :=
  (Corepresented.affinePointsEquiv (functor R n) (corepresentableBy R n) A x).toAdd

/-- Affine coordinates determine the point of the vector group. -/
theorem affineCoordinates_injective (A : CommAlgCat.{u} R) :
    Function.Injective (affineCoordinates (R := R) (n := n) A) := by
  intro x y h
  apply (Corepresented.affinePointsEquiv (functor R n) (corepresentableBy R n) A).injective
  exact Multiplicative.toAdd.injective h

/-- Equality of the coordinates on every affine test detects homomorphisms to a
vector group. -/
theorem hom_ext_affineCoordinates (f g : G ⟶ groupScheme R n)
    (h : ∀ (A : CommAlgCat.{u} R) (x : G.affinePoints A) (i : Fin n),
      (Corepresented.affinePointsEquiv (functor R n) (corepresentableBy R n) A
        (x ≫ f.hom.hom)).toAdd i =
      (Corepresented.affinePointsEquiv (functor R n) (corepresentableBy R n) A
        (x ≫ g.hom.hom)).toAdd i) :
    f = g := by
  apply AffinePointComparison.hom_ext G f g
  intro A x
  apply affineCoordinates_injective A
  exact funext (h A x)

/-- Vanishing of every affine coordinate of every homomorphism to a vector group
implies uniqueness of such homomorphisms. -/
theorem subsingleton_hom_of_affineCoordinates_eq_zero
    (h : ∀ (f : G ⟶ groupScheme R n) (A : CommAlgCat.{u} R)
      (x : G.affinePoints A) (i : Fin n),
      (Corepresented.affinePointsEquiv (functor R n) (corepresentableBy R n) A
        (x ≫ f.hom.hom)).toAdd i = 0) :
    Subsingleton (G ⟶ groupScheme R n) := by
  refine ⟨fun f g => hom_ext_affineCoordinates f g ?_⟩
  intro A x i
  exact (h f A x i).trans (h g A x i).symm

end Langlands.GroupScheme.VectorGroup
