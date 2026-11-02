import Langlands.GroupScheme.Lie.GroupAlgebraCoordinates
import Langlands.GroupScheme.Torus.Weights
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Finite dimension of the actual Lie kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] coordinateOriginAlgebra

/-- A derivation at the identity is determined by its values on a finite set
of algebra generators. -/
theorem finiteDimensional_identityDerivation :
    FiniteDimensional k (IdentityDerivation G (A := k)) := by
  classical
  have := coordinateAlgebraFiniteType G
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := coordinateAlgebra G)
  let ev : IdentityDerivation G (A := k) →ₗ[k] (s → k) :=
    { toFun := fun d a => d a
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply FiniteDimensional.of_injective ev
  intro d e h
  apply Derivation.ext_of_adjoin_eq_top (s : Set (coordinateAlgebra G)) hs
  intro a ha
  exact congrFun h ⟨a, ha⟩

/-- The actual dual-number identity kernel of an affine locally finite type
group over a field is finite-dimensional. -/
instance finiteDimensional_lieKernel :
    FiniteDimensional k (Additive (lieKernel G k)) := by
  have := finiteDimensional_identityDerivation G
  exact (kernelDerivationLinearEquiv G (A := k)).symm.finiteDimensional

end Langlands.GroupScheme.Lie
