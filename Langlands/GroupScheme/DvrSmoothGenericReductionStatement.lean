import Langlands.GroupScheme.DvrFiniteSmoothCoverStatement

/-! # Finite group covers with smooth generic fibre after a DVR extension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A preliminary finite cover for which the actual generic fibre is smooth.
Smoothness of the whole covering group is a separate assertion. -/
def DvrSmoothGenericReductionStatement : Prop :=
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
          ∃ (P : GroupScheme (Spec (CommRingCat.of R')))
            (q : P ⟶ (baseChange b).obj G),
            Flat P.X.hom ∧ LocallyOfFiniteType P.X.hom ∧
            QuasiCompact P.X.hom ∧ IsSeparated P.X.hom ∧
            Smooth
              ((baseChange (Spec.algebraMap R' (FractionRing R'))).obj P).X.hom ∧
            IsAffineHom
              ((baseChange (Spec.algebraMap R' (FractionRing R'))).obj P).X.hom ∧
            IsFinite q.hom.hom.left ∧ Surjective q.hom.hom.left

end Langlands.GroupScheme
