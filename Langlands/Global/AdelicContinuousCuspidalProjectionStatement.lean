import Langlands.Global.AdelicCuspidalAnnihilator

/-! # Continuous cuspidal projections of automorphic functions on parabolic quotients -/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Every automorphic function `φ` on `U_Q(𝔸) M_Q(F) \ G(𝔸)`, for a standard parabolic `Q` of
a compatible standard family, has a continuous cuspidal projection: a continuous function `ψ`
of moderate growth on the same quotient, cuspidal along `Q`, whose norm-one Levi pairings with
every Levi cusp form at every point of `G(𝔸)` converge absolutely and agree with those of `φ`
(Bernstein–Lapid §6.2, (6.8); Mœglin–Waldspurger I.2.18 and I.3.5). The projection is required
to be continuous of moderate growth only, not automorphic. The compact serves the minimal
standard parabolic and its intersections with the standard Levis are maximal. -/
def ContinuousCuspidalProjectionExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G)),
    IsMaximalCompactSubgroup F G K →
    IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K →
    (∀ J : StandardIndex F G fam.i fam.ν,
      IsMaximalCompactSubgroup F (fam.M J)
        (K.comap (AdelicGroupPoints.map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom),
      IsClosedSubgroup rho →
      let Kinf := K.comap (ofInfinite F G).toMonoidHom
      ∀ (Q : StandardIndex F G fam.i fam.ν) (φ : AdelicGroupPoints F G → ℂ),
        fam.IsAutomorphicOn hsmooth Kinf rho Q φ →
          ∃ ψ : AdelicGroupPoints F G → ℂ,
            fam.IsModerateContinuousOnParabolic rho Q ψ ∧ fam.IsCuspidalAlong Q ψ ∧
            ∀ t : AdelicGroupPoints F (fam.M Q) → ℂ, fam.IsLeviCuspForm Kinf rho Q t →
              ∀ g : AdelicGroupPoints F G,
                Integrable (fam.leviPairingIntegrand Q φ g t)
                    (normOneRationalQuotientHaarMeasure F (fam.M Q)) ∧
                  Integrable (fam.leviPairingIntegrand Q ψ g t)
                    (normOneRationalQuotientHaarMeasure F (fam.M Q)) ∧
                  fam.leviPairing Q φ g t = fam.leviPairing Q ψ g t

end Langlands.Global
