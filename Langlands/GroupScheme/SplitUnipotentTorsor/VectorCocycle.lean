import Langlands.GroupScheme.TorsorCocycle
import Langlands.AlgebraicGeometry.AffineAdditiveCocycle
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Cocycles valued in a one-dimensional vector group

Over an affine scheme, a natural cocycle on an affine flat surjective cover with values in
the base change of a one-dimensional vector group is trivial. Natural coordinates turn it
into an additive cocycle valued in global functions, which is a coboundary by degree-one
exactness of the Amitsur complex.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot Langlands.AlgebraicGeometry.AffineAdditiveCocycle

variable {B : Scheme.{u}} {V : GroupScheme B}

namespace VectorCocycle

variable {n : ℕ} (e : ∀ W : Over B, (W ⟶ V.X) ≃* Multiplicative (Fin n → Γ(W.left, ⊤)))
  (T : Over B)

/-- Coordinates on the points of the base change of `V` to `T`, read through the pullback
adjunction on points. -/
def baseChangeCoordinates (Z : Over T.left) :
    (Z ⟶ ((GroupScheme.baseChange T.hom).obj V).X) ≃*
      Multiplicative (Fin n → Γ(Z.left, ⊤)) :=
  (baseChangePointsEquiv T.hom V Z).trans (e ((Over.map T.hom).obj Z))

/-- Natural coordinates stay natural after base change. -/
theorem baseChangeCoordinates_comp
    (he : ∀ (W W' : Over B) (b : W' ⟶ W) (x : W ⟶ V.X),
      (e W' (b ≫ x)).toAdd = fun j => b.left.appTop ((e W x).toAdd j))
    {Z Z' : Over T.left} (t : Z' ⟶ Z) (x : Z ⟶ ((GroupScheme.baseChange T.hom).obj V).X) :
    (baseChangeCoordinates e T Z' (t ≫ x)).toAdd =
      fun j => t.left.appTop ((baseChangeCoordinates e T Z x).toAdd j) := by
  simp only [baseChangeCoordinates, MulEquiv.trans_apply, baseChangePointsEquiv_naturality]
  exact he _ _ ((Over.map T.hom).map t) _

end VectorCocycle

/-- Over an affine scheme, every natural cocycle on an affine flat surjective cover with
values in the base change of a one-dimensional vector group is trivial. -/
theorem Cocycle.isTrivial_of_isVectorGroupOfDimension_one (hV : IsVectorGroupOfDimension V 1)
    (T : Over B) [IsAffine T.left] (U : Over T.left) [IsAffine U.left] [Flat U.hom]
    [Surjective U.hom] (ξ : Cocycle ((GroupScheme.baseChange T.hom).obj V) U) :
    ξ.IsTrivial := by
  obtain ⟨e, he⟩ := hV
  let coord := VectorCocycle.baseChangeCoordinates e T
  have hcoord := @VectorCocycle.baseChangeCoordinates_comp _ _ _ e T he
  let α : AddCocycle U :=
    { toFun := fun a b => (coord _ (ξ.toFun a b)).toAdd 0
      naturality := fun t a b => by
        simp only [coord]
        rw [ξ.naturality, hcoord]
      cocycle := fun a b c => by
        simp only [coord]
        rw [ξ.cocycle a b c, map_mul, toAdd_mul, Pi.add_apply] }
  obtain ⟨β, hβ⟩ := α.exists_coboundary
  refine ⟨(coord U).symm (Multiplicative.ofAdd fun _ => β), fun {Z} a b => ?_⟩
  apply (coord Z).injective
  apply Multiplicative.toAdd.injective
  funext j
  rw [Fin.fin_one_eq_zero j, map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply,
    Pi.neg_apply, hcoord, hcoord, MulEquiv.apply_symm_apply, toAdd_ofAdd, ← sub_eq_add_neg]
  exact hβ a b

end Langlands.GroupScheme
