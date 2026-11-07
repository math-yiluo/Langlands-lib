import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: a split fibrewise-maximal torus over a local ring has a constant root datum -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For a reductive group over a local ring and a closed coordinate split torus in it that is
maximal on every residue-field fibre, some finite reduced root datum on the coordinate lattices
`I → ℤ` is the actual root datum of the torus on every field-valued fibre. -/
def LocalSplitFibrewiseRootDatumExistenceStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i →
      (∀ s : Spec (CommRingCat.of R),
        IsMaximalTorus
          (T := (CommGroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj
              (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I))
          ((GroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map i)) →
      ∃ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P

end Langlands.GroupScheme
