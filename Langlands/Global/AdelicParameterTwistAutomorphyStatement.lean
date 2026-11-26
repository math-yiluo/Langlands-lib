import Langlands.Global.AdelicEisensteinSeries
import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Twists of automorphic forms on a parabolic quotient

Bernstein–Lapid §2.2: for an automorphic form `φ` on `X_P = U(𝔸) M(F) \ G(𝔸)` and
`λ ∈ X^*(P) ⊗ ℂ`, the twist `φ_λ(g) = φ(g) m_P(g)^λ` is again an automorphic form on `X_P`.
Stated here for the standard parabolics of a standard family and a maximal compact subgroup in
good position. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Twisting preserves automorphy on a standard parabolic quotient (Bernstein–Lapid §2.2).
Let `fam` be a standard parabolic family of a group over a number field, `I` a standard index
and `K` a maximal compact subgroup of `G(𝔸)` with `hK : P_I(𝔸) K = G(𝔸)`, Iwasawa coverage for
the minimal standard parabolic and maximal compact intersections with all standard Levis. If `φ`
is automorphic on `U_I(𝔸) M_I(F) \ G(𝔸)` for the archimedean part of `K` and a closed matrix
embedding `rho`, then so is `φ_λ = hK.parameterTwist φ λ` for every `λ ∈ X^*(P_I) ⊗ ℂ`. -/
def ParameterTwistAutomorphyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (I : StandardIndex F G fam.i fam.ν)
    [IsClosedImmersion (fam.p I).hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p I) K),
      IsMaximalCompactSubgroup F G K →
      IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K →
      (∀ J : StandardIndex F G fam.i fam.ν,
        IsMaximalCompactSubgroup F (fam.M J)
          (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) →
      ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
        (hsmooth : SmoothOfRelativeDimension d G.X.hom),
        IsClosedSubgroup rho →
        ∀ phi : AdelicGroupPoints F G → ℂ,
          fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I phi →
          ∀ lam : ComplexCharacterParameter F (fam.P I),
            fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I
              (hK.parameterTwist phi lam)

end Langlands.Global
