import Langlands.GroupScheme.Reductive.FibrewiseIsogenyStatement
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian

/-! # Removing the closed-fibre kernel over a strictly Henselian DVR -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A homomorphism of reductive groups over a strictly Henselian DVR that is
an isogeny on every fibre factors through an isogeny from its source, so that
the remaining homomorphism is an isomorphism on the closed fibre and remains
an isogeny on every fibre. -/
def StrictHenselianDvrKernelRemovalStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    ∀ (f : G ⟶ H),
      (∀ s : Spec (CommRingCat.of R),
        IsIsogeny ((baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map f)) →
      ∃ (Q : GroupScheme (Spec (CommRingCat.of R))) (q : G ⟶ Q) (g : Q ⟶ H),
        IsReductive Q ∧ IsIsogeny q ∧ q ≫ g = f ∧
          (∀ s : Spec (CommRingCat.of R),
            IsIsogeny
              ((baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map g)) ∧
          IsIso ((baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).map g)

end Langlands.GroupScheme
