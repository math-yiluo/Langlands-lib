import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Exponent decomposition of automorphic functions on parabolic quotients -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Every automorphic function on `U_Q(𝔸) M_Q(F) \ G(𝔸)`, for a standard parabolic `Q` of a
compatible standard family, is a finite sum of automorphic functions with generalized
unnormalized exponents for the left action of the positive split component of `Q`; if the
function is cuspidal along `Q`, so are the summands (Mœglin–Waldspurger I.3.1–I.3.3;
Bernstein–Lapid §6.2, (6.3) and (6.6), and §6.3, (6.10)). The compact serves the minimal
standard parabolic and its intersections with the standard Levis are maximal. -/
def AutomorphicExponentDecompositionStatement : Prop :=
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
      ∀ (Q : StandardIndex F G fam.i fam.ν) (ψ : AdelicGroupPoints F G → ℂ),
        fam.IsAutomorphicOn hsmooth Kinf rho Q ψ →
          ∃ (s : Finset (ComplexCharacterParameter F (fam.P Q)))
              (c : ComplexCharacterParameter F (fam.P Q) → AdelicGroupPoints F G → ℂ),
            ψ = ∑ lam ∈ s, c lam ∧
            ∀ lam ∈ s, fam.IsAutomorphicOn hsmooth Kinf rho Q (c lam) ∧
              fam.HasUnnormalizedExponent Q lam (c lam) ∧
              (fam.IsCuspidalAlong Q ψ → fam.IsCuspidalAlong Q (c lam))

end Langlands.Global
