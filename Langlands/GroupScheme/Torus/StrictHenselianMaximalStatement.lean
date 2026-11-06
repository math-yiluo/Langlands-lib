import Langlands.GroupScheme.Torus.Maximal
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian

/-! # Split maximal tori over strictly Henselian local rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A reductive group over a strictly Henselian local ring contains an actual
closed split torus whose inclusion is maximal on every residue-field fibre. -/
def StrictHenselianSplitMaximalTorusStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (G : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G →
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of R))) (i : T.toGrp ⟶ G),
      IsSplitTorus T.toGrp ∧ IsClosedSubgroup i ∧
      ∀ s : Spec (CommRingCat.of R),
        IsMaximalTorus
          (T := (CommGroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj T)
          ((GroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map i)

end Langlands.GroupScheme
