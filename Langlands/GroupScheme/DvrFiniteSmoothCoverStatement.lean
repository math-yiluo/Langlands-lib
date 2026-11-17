import Langlands.GroupScheme.DvrGenericAffinenessStatement
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Finite smooth covers after a faithfully flat DVR extension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- After a faithfully flat DVR extension, a flat separated finite-type group
with affine generic fibre admits a finite surjective smooth group cover. -/
def DvrFiniteSmoothCoverStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of R))),
    Flat G.X.hom → LocallyOfFiniteType G.X.hom → QuasiCompact G.X.hom →
    IsSeparated G.X.hom →
    IsAffineHom
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G).X.hom →
    ∃ (R' : Type u) (cR' : CommRing R'),
      letI := cR'
      ∃ (dR' : IsDomain R'),
        letI := dR'
        ∃ (_ : IsDiscreteValuationRing R')
          (b : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)),
          Flat b ∧ Surjective b ∧
          ∃ (H : GroupScheme (Spec (CommRingCat.of R')))
            (π : H ⟶ (baseChange b).obj G),
            Smooth H.X.hom ∧ QuasiCompact H.X.hom ∧ IsSeparated H.X.hom ∧
            IsAffineHom
              ((baseChange (Spec.map
                (CommRingCat.ofHom (algebraMap R' (FractionRing R'))))).obj H).X.hom ∧
            IsFinite π.hom.hom.left ∧ Surjective π.hom.hom.left

end Langlands.GroupScheme
