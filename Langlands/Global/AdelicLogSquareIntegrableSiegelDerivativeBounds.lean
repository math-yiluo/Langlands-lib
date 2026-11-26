import Langlands.Global.AdelicTemperedVanishingReduction
import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Langlands.Global.AdelicMaximalUnipotentDecay

/-! # Logarithmic Siegel bounds for the derivatives of weighted square-integrable forms

Delorme 2023, Proposition 3.5 ((ii) implies (i)) with Lemma 3.2 and Definition 3.3, for the
automorphic forms of `TemperedWeakConstantTermVanishingStatement`. The weighted `L²` hypothesis
is the one of `IsLogSquareIntegrableAutomorphicForm`, on the form itself and not on its
derivatives. The conclusion is a bound on the Siegel sets of `IsSiegelPoint` by the square root
of the modulus `siegelModulus` of the torus coordinate times a power of the logarithmic height
`adelicLogHeight` of the point, for every word of archimedean right-orbit derivatives
(`adelicIteratedDirectionalValue`). This file states the proposition and does not prove it. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints AdelicSiegelFactors

/-- **Logarithmic Siegel bounds for all derivatives of a weighted square-integrable automorphic
form** (Delorme 2023, Proposition 3.5, (ii) implies (i), in the form c) of Lemma 3.2 for `P = G`,
with Definition 3.3; the derivative bounds come from Bernstein 1988, Key Lemma p.686). Take the
hypotheses of `TemperedWeakConstantTermVanishingStatement` through the one on `Φ`: a number
field `F`, a connected reductive `G`, a maximal compact `K ⊆ G(𝔸)` with `P_∅(𝔸) K = G(𝔸)` for
a compatible family `𝓕` of standard parabolics, a closed matrix embedding `rho`, and `Φ` with
`IsLogSquareIntegrableAutomorphicForm` (an automorphic form for the archimedean part of `K` with
a unitary `A_G`-character and `Φ / σ_{[G]}^m ∈ L²([G])` for some `m`). Then for every algebraic
Siegel setup `(T, i, ν, T₀, j)`, compact factors `C` (whose compact subgroup need not be `K`),
threshold `t` and compact `Ω ⊆ G(𝔸)` there is `m : ℕ` such that for every word `D` of
archimedean tangent directions there is `C_D ≥ 0` with
`‖D Φ(x)‖ ≤ C_D δ₀(a)^{1/2} σ(x)^m` at every point `x = z · n m a k · w` of the Siegel set
`A_G · Ω_N Ω_M A_{T₀}(t) K_C · Ω` with torus coordinate `a`. Here `δ₀ = siegelModulus` and
`σ = adelicLogHeight`, the height of the point itself, while the hypothesis uses the quotient
height `σ_{[G]} = rationalLogHeight`, with `σ_{[G]}(G(F) x) ≤ σ(x)`
(`rationalLogHeight_mk_le`). The empty word gives the bound for `Φ`. -/
def LogSquareIntegrableSiegelDerivativeBoundsStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (𝓕 : StandardParabolicFamily F G), IsIwasawaCompact (𝓕.p 𝓕.bot) K →
    ∀ Φ : AdelicGroupPoints F G → ℂ,
      IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
        (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j →
      ∀ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
        (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω →
      ∃ m : ℕ, ∀ D : List (smoothModel F d), ∃ C_D : ℝ, 0 ≤ C_D ∧
        ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀) (x : AdelicGroupPoints F G),
          IsSiegelPoint F G T i ν T₀ j C t Ω a x →
            ‖adelicIteratedDirectionalValue hsmooth D Φ x‖ ≤
              C_D * Real.sqrt (siegelModulus F G T i ν T₀ j a) *
                adelicLogHeight F G rho x ^ m

end Langlands.Global
