import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Automorphy of Eisenstein series in the region of absolute convergence

Bernstein–Lapid, Theorem 2.3 (1): for `φ` automorphic on `U(𝔸)M(F) \ G(𝔸)`, the Eisenstein
series `E(φ, λ)`, defined and holomorphic for `Re λ` sufficiently regular, is an automorphic
form on `G(F) \ G(𝔸)` there. Stated here for the standard parabolics of a standard family and a
maximal compact subgroup in good position. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Automorphy of convergent Eisenstein series (Bernstein–Lapid, Theorem 2.3 (1), in the region
of absolute convergence). Let `fam` be a standard parabolic family of a group over a number
field, `I` a standard index and `K` a maximal compact subgroup of `G(𝔸)` with
`hK : P_I(𝔸) K = G(𝔸)`, Iwasawa coverage for the minimal standard parabolic and maximal compact
intersections with all standard Levis. If `φ` is automorphic on `U_I(𝔸) M_I(F) \ G(𝔸)` for the
archimedean part `K_∞` of `K` and a closed matrix embedding `rho`, there is `R` such that for
every `R`-regular `λ` the Eisenstein series `E(φ, λ)` is automorphic on `G(F) \ G(𝔸)` for `K_∞`,
`rho` and the canonical commutator datum. -/
def EisensteinRegularAutomorphyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (I : StandardIndex F G fam.i fam.ν)
    [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
    [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p I) K),
      IsMaximalCompactSubgroup F G K →
      IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K →
      (∀ J : StandardIndex F G fam.i fam.ν,
        IsMaximalCompactSubgroup F (fam.M J)
          (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) →
      ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
        (hsmooth : SmoothOfRelativeDimension d G.X.hom),
        IsClosedSubgroup rho →
        let Kinf := K.comap (ofInfinite F G).toMonoidHom
        let r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I) :=
          ⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩
        let hA := (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
        let hT := fam.maximalSplit.isSplitSubtorus.1
        ∀ phi : AdelicGroupPoints F G → ℂ,
          fam.IsAutomorphicOn hsmooth Kinf rho I phi →
          ∃ R : ℝ, ∀ lam : ComplexCharacterParameter F (fam.P I),
            r.IsRegularParameter hA hT R lam →
            IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
              (rationalSubgroup F G) Kinf rho (hK.eisensteinSeries phi lam)

end Langlands.Global
