import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: the Isomorphism Theorem for split reductive groups over a reduced local ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Two reductive groups over a reduced local ring, each with a closed coordinate split torus
that is maximal on every residue-field fibre and carries a fibrewise root datum, are isomorphic as
soon as the two root data are equivalent. -/
def LocalSplitReducedIsomorphismTheoremStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsReduced R]
    (G H : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom] [IsAffineHom H.X.hom],
    IsReductive G → IsReductive H →
    ∀ (I I' : Type u) [Fintype I] [Fintype I']
      (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
      (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H),
      IsClosedSubgroup i → IsClosedSubgroup i' →
      (∀ s : Spec (CommRingCat.of R),
        IsMaximalTorus
          (T := (CommGroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj
              (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I))
          ((GroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map i)) →
      (∀ s : Spec (CommRingCat.of R),
        IsMaximalTorus
          (T := (CommGroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj
              (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I'))
          ((GroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map i')) →
      ∀ (J J' : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ)),
        IsFibrewiseRootDatumOf I G i P → IsFibrewiseRootDatumOf I' H i' Q →
        Nonempty (RootPairing.Equiv P Q) →
        Nonempty (G ≅ H)

end Langlands.GroupScheme
