import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Existence of cuspidal projections of automorphic functions on parabolic quotients -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Every automorphic function on `U_Q(𝔸) M_Q(F) \ G(𝔸)`, for a standard parabolic `Q` of a
compatible standard family, has a cuspidal projection characterized by the norm-one Levi
pairings (Mœglin–Waldspurger I.2.18 and I.3.5; Bernstein–Lapid §6.2, (6.8)). The compact
serves the minimal standard parabolic and its intersections with the standard Levis are
maximal. -/
def CuspidalProjectionExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G)),
    IsMaximalCompactSubgroup F G K →
    IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K →
    (∀ J : StandardIndex F G fam.i fam.ν,
      IsMaximalCompactSubgroup F (fam.M J)
        (K.comap (AdelicGroupPoints.map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom),
      IsClosedSubgroup rho →
      let Kinf := K.comap (ofInfinite F G).toMonoidHom
      ∀ (Q : StandardIndex F G fam.i fam.ν) (φ : AdelicGroupPoints F G → ℂ),
        fam.IsAutomorphicOn hsmooth Kinf rho Q φ →
          ∃ ψ : AdelicGroupPoints F G → ℂ, fam.IsCuspidalProjection hsmooth Kinf rho Q φ ψ

end Langlands.Global
