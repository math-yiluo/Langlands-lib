import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.RingTheory.Henselian

/-! # Statement: a clopen diagonalizable lift over a strictly Henselian base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The intermediate lifting assertion in Conrad's proof of Theorem B.4.1:
a diagonalization of the special fibre lifts to an open and closed
diagonalizable subgroup over a strictly Henselian local base. -/
def MultiplicativeTypeStrictHenselianLiftStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (H : GroupScheme (Spec (CommRingCat.of A)))
    [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom] [IsAffineHom H.X.hom],
    (∀ s : Spec (CommRingCat.of A), IsMultiplicativeType (geometricFiber H s)) →
      ∀ (M : Type u) [AddCommGroup M] [AddGroup.FG M],
        let sp := Spec.algebraMap A (IsLocalRing.ResidueField A)
        ∀ e : (GroupScheme.baseChange sp).obj
            (RelativeMultiplicativeType.diagonalizable (Spec (CommRingCat.of A)) M) ≅
              (GroupScheme.baseChange sp).obj H,
          ∃ j : RelativeMultiplicativeType.diagonalizable (Spec (CommRingCat.of A)) M ⟶ H,
            (GroupScheme.baseChange sp).map j = e.hom ∧
              IsOpenImmersion j.hom.hom.left ∧ IsClosedImmersion j.hom.hom.left

end Langlands.GroupScheme
