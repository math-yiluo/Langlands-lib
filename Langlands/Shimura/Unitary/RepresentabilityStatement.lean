import Langlands.Shimura.Unitary.Similitude
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.FinitePresentation
import Mathlib.CategoryTheory.Yoneda

/-! # Affine representability target for the rational similitude functor -/

universe u

namespace Langlands.Shimura

open CategoryTheory Opposite

/-- The actual rational similitude functor of a finite-dimensional algebra
is represented by a finitely presented commutative rational algebra.
The representing algebra and natural isomorphism are conclusions. -/
def SimilitudeRepresentabilityStatement : Prop :=
  ∀ (A : Type u) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A]
    (σ : AlgebraInvolution ℚ A),
    ∃ B : CommAlgCat.{u} ℚ, Algebra.FinitePresentation ℚ B ∧
      Nonempty
        (coyoneda.obj (op B) ≅
          (σ.similitudeFunctor : CommAlgCat.{u} ℚ ⥤ GrpCat.{u}) ⋙
            forget GrpCat.{u})

end Langlands.Shimura
