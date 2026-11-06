import Langlands.GroupScheme.Torus.Maximal
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Split reductive groups over a local ring are determined by a geometric fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Two reductive groups over a local ring, each containing an actual closed split torus whose
inclusion is maximal on every residue-field fibre, are isomorphic as soon as their base changes
to some algebraically closed field over the ring are isomorphic. -/
def LocalSplitReductiveGeometricIsoStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    (∃ (T : CommGroupScheme (Spec (CommRingCat.of R))) (i : T.toGrp ⟶ G),
      IsSplitTorus T.toGrp ∧ IsClosedSubgroup i ∧
      ∀ s : Spec (CommRingCat.of R),
        IsMaximalTorus
          (T := (CommGroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj T)
          ((GroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map i)) →
    (∃ (T : CommGroupScheme (Spec (CommRingCat.of R))) (i : T.toGrp ⟶ H),
      IsSplitTorus T.toGrp ∧ IsClosedSubgroup i ∧
      ∀ s : Spec (CommRingCat.of R),
        IsMaximalTorus
          (T := (CommGroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj T)
          ((GroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map i)) →
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω],
      Nonempty (((GroupScheme.baseChange (Spec.algebraMap R Ω)).obj G) ≅
        ((GroupScheme.baseChange (Spec.algebraMap R Ω)).obj H)) →
      Nonempty (G ≅ H)

end Langlands.GroupScheme
