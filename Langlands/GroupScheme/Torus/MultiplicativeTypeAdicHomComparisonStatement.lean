import Langlands.GroupScheme.HomScheme.AdicSystem
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Statement: effectivity of compatible homomorphisms from isotrivial groups of
multiplicative type over an adically complete noetherian ring -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType

/-- SGA 3, Exposé IX, Théorème 7.1: restriction to the adic thickenings identifies actual
homomorphisms from an isotrivial group of multiplicative type to an affine group with
compatible systems of such homomorphisms. -/
def MultiplicativeTypeAdicHomComparisonStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (H G : GroupScheme (Spec (CommRingCat.of A))) [IsAffineHom G.X.hom],
    (∃ (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of A)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        IsDiagonalizable ((GroupScheme.baseChange p).obj H)) →
      Function.Bijective (HomScheme.Adic.System.restrict I H G)

end Langlands.GroupScheme
