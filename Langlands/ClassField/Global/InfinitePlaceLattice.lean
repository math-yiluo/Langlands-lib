import Langlands.GroupTheory.CocycleCohomology
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # The integer permutation lattice on infinite places -/

noncomputable section

open NumberField CategoryTheory
open scoped BigOperators

namespace Langlands.ClassField.Global

universe u v

variable (F : Type u) [Field F] (E : Type v) [Field E] [Algebra F E]

/-- The free module on the actual infinite places, with the arithmetic permutation action. -/
abbrev infinitePlaceLatticeRepresentation :
    Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E) :=
  Rep.ofMulAction NormalizedTwoCocycle.CoefficientScalars (E ≃ₐ[F] E) (InfinitePlace E)

/-- The action sends the basis vector at `w` to the basis vector at `g • w`. -/
@[simp] theorem infinitePlaceLatticeRepresentation_single (g : E ≃ₐ[F] E)
    (w : InfinitePlace E) (a : NormalizedTwoCocycle.CoefficientScalars.{v}) :
    (infinitePlaceLatticeRepresentation F E).ρ g (MonoidAlgebra.single w a) =
      MonoidAlgebra.single (g • w) a :=
  Representation.ofMulAction_single g w a

/-- Coefficients transform by inverse precomposition with the arithmetic action. -/
@[simp] theorem infinitePlaceLatticeRepresentation_coeff (g : E ≃ₐ[F] E)
    (x : (infinitePlaceLatticeRepresentation F E).V) (w : InfinitePlace E) :
    ((infinitePlaceLatticeRepresentation F E).ρ g x).coeff w = x.coeff (g⁻¹ • w) :=
  Representation.coeff_ofMulAction g x w

variable [NumberField E]

/-- The finite free module is the module of functions from infinite places to lifted integers. -/
def infinitePlaceLatticeFunctionEquiv :
    (infinitePlaceLatticeRepresentation F E).V ≃ₗ[NormalizedTwoCocycle.CoefficientScalars.{v}]
      (InfinitePlace E → NormalizedTwoCocycle.CoefficientScalars.{v}) :=
  (MonoidAlgebra.coeffLinearEquiv _).trans (Finsupp.linearEquivFunOnFinite _ _ _)

@[simp] theorem infinitePlaceLatticeFunctionEquiv_apply
    (x : (infinitePlaceLatticeRepresentation F E).V) (w : InfinitePlace E) :
    infinitePlaceLatticeFunctionEquiv F E x w = x.coeff w := rfl

/-- The function realization has precisely Milne's inverse-precomposition action. -/
theorem infinitePlaceLatticeFunctionEquiv_action (g : E ≃ₐ[F] E)
    (x : (infinitePlaceLatticeRepresentation F E).V) (w : InfinitePlace E) :
    infinitePlaceLatticeFunctionEquiv F E
        ((infinitePlaceLatticeRepresentation F E).ρ g x) w =
      infinitePlaceLatticeFunctionEquiv F E x (g⁻¹ • w) :=
  infinitePlaceLatticeRepresentation_coeff F E g x w

/-- Sum of the coordinates of an infinite-place lattice element. -/
def infinitePlaceLatticeSum :
    (infinitePlaceLatticeRepresentation F E).V →ₗ[NormalizedTwoCocycle.CoefficientScalars.{v}]
      NormalizedTwoCocycle.CoefficientScalars.{v} where
  toFun x := ∑ w : InfinitePlace E, x.coeff w
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply]
    exact Finset.smul_sum.symm

@[simp] theorem infinitePlaceLatticeSum_apply
    (x : (infinitePlaceLatticeRepresentation F E).V) :
    infinitePlaceLatticeSum F E x = ∑ w : InfinitePlace E, x.coeff w := rfl

/-- Coordinate sum is invariant under the arithmetic permutations. -/
theorem infinitePlaceLatticeSum_action (g : E ≃ₐ[F] E)
    (x : (infinitePlaceLatticeRepresentation F E).V) :
    infinitePlaceLatticeSum F E ((infinitePlaceLatticeRepresentation F E).ρ g x) =
      infinitePlaceLatticeSum F E x := by
  change (∑ w : InfinitePlace E,
    ((infinitePlaceLatticeRepresentation F E).ρ g x).coeff w) = ∑ w, x.coeff w
  simp only [Representation.coeff_ofMulAction]
  exact Equiv.sum_comp (MulAction.toPerm (g⁻¹)) (fun w => x.coeff w)

/-- The coordinate-sum map as a morphism to the trivial lifted-integer representation. -/
def infinitePlaceLatticeAugmentation :
    infinitePlaceLatticeRepresentation F E ⟶
      Rep.trivial NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E)
        NormalizedTwoCocycle.CoefficientScalars.{v} :=
  Rep.ofHom
    { toLinearMap := infinitePlaceLatticeSum F E
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        exact infinitePlaceLatticeSum_action F E g x }

/-- Ordinary group cohomology of the actual infinite-place permutation lattice. -/
abbrev infinitePlaceLatticeCohomology (n : ℕ) :
    ModuleCat.{v} NormalizedTwoCocycle.CoefficientScalars.{v} :=
  groupCohomology (infinitePlaceLatticeRepresentation F E) n

end Langlands.ClassField.Global
