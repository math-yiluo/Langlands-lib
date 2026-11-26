import Langlands.Global.AdelicEisensteinSeries
import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Center finiteness of twists on a parabolic quotient

The `𝔷`-finiteness part of Bernstein–Lapid §2.2, p. 191 ("`φ_λ ∈ 𝒜_P`"): for a smooth function
`φ` on `U(𝔸) \ G(𝔸)` that is finite under the center `𝔷(𝔤)` of the complex enveloping algebra,
and `λ ∈ X^*(P) ⊗ ℂ`, the twist `φ_λ(g) = φ(g) m_P(g)^λ` is again `𝔷`-finite. Stated for the
standard parabolics of a standard family and a maximal compact subgroup `K` of `G(𝔸)` with
`P(𝔸) K = G(𝔸)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Twisting preserves `𝔷`-finiteness on `U_I(𝔸) \ G(𝔸)` (Bernstein–Lapid §2.2, p. 191, the
center-finiteness part of `φ_λ ∈ 𝒜_P`). Let `fam` be a standard parabolic family of a group over
a number field, `I` a standard index and `K` a maximal compact subgroup of `G(𝔸)` with
`hK : P_I(𝔸) K = G(𝔸)`. Let `φ` be a function on `G(𝔸)` that is left invariant under the image
of `U_I(𝔸)`, smooth, and `𝔷`-finite for the commutator datum `hcalc`. Then for every
`λ ∈ X^*(P_I) ⊗ ℂ` the twist `φ_λ = hK.parameterTwist φ λ` is `𝔷`-finite. -/
def ParameterTwistCenterFiniteStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (I : StandardIndex F G fam.i fam.ν)
    [IsClosedImmersion (fam.p I).hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p I) K),
      IsMaximalCompactSubgroup F G K →
      ∀ {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
        (hcalc : AdelicDifferentialCommutator F G hsmooth)
        (phi : AdelicGroupPoints F G → ℂ),
        IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I) (fam.iU I)) phi →
        IsAdelicSmoothFunction F G phi →
        IsCenterFiniteFunction F G hsmooth hcalc phi →
        ∀ lam : ComplexCharacterParameter F (fam.P I),
          IsCenterFiniteFunction F G hsmooth hcalc (hK.parameterTwist phi lam)

end Langlands.Global
