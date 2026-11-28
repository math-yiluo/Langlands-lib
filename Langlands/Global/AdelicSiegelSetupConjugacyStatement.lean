import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction

/-! # Rational conjugacy of Siegel sets of two algebraic Siegel setups

`SiegelSetupConjugacyStatement`: for two algebraic Siegel setups `S = (T, i, ν, T₀, j)` and
`S' = (T', i', ν', T₀', j')` of a connected reductive group `G` over a number field `F`, every
Siegel set `A_G · Ω_N Ω_M A_{T₀}(t) K · Ω` of `S` is carried by left translation by one rational
point `q ∈ G(F)` into a Siegel set of `S'`, with a torus coordinate of the same modulus. This is
the adelic form of the rational conjugacy of pairs (minimal parabolic, maximal split torus in
it), Borel–Tits 1965, Théorème 4.13 b), Proposition 4.7, Corollaire 4.16 and Théorème 4.21.
This file states the proposition and does not prove it. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors

/-- **Rational conjugacy of Siegel sets of two algebraic Siegel setups** (derived from
Borel–Tits 1965, Théorème 4.13 b), Proposition 4.7, Corollaire 4.16 and Théorème 4.21, for the
Siegel sets of Mœglin–Waldspurger I.2.1 and Delorme 2023, (2.3)). Let `G` be a connected
reductive group over a number field `F` and `(T, i, ν, T₀, j)`, `(T', i', ν', T₀', j')` two
algebraic Siegel setups of `G`. For all compact factors `C` of the first setup (with any compact
subgroup), every threshold `t` and every compact `Ω ⊆ G(𝔸)` there are a rational point
`q ∈ G(F)`, compact factors `C'` of the second setup, a threshold `t'` and a compact
`Ω' ⊆ G(𝔸)` such that for every point `x` of the Siegel set of `(C, t, Ω)` with torus
coordinate `a`, the point `q x` lies in the Siegel set of `(C', t', Ω')` with a torus coordinate
`a'` with `δ'(a') = δ(a)`, where `δ` and `δ'` are the moduli `siegelModulus` of the two
setups. -/
def SiegelSetupConjugacyStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
      (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j →
    ∀ (T' : CommGroupScheme (Spec (CommRingCat.of F))) (i' : T'.toGrp ⟶ G)
      (ν' : cocharacterLattice T') (T₀' : CommGroupScheme (Spec (CommRingCat.of F)))
      (j' : T₀' ⟶ T'), IsSiegelAlgebraicSetup F G T' i' ν' T₀' j' →
    ∀ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
      (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω →
    ∃ q ∈ rationalSubgroup F G,
      ∃ (C' : CompactFactors F G (Standard.unipotentScheme i' ν' ∅)
          (Standard.leviScheme i' ν' ∅))
        (t' : ℝ≥0ˣ) (Ω' : Set (AdelicGroupPoints F G)), IsCompact Ω' ∧
      ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀) (x : AdelicGroupPoints F G),
        IsSiegelPoint F G T i ν T₀ j C t Ω a x →
        ∃ a' : PositiveRealTorus.intrinsicSubgroup F T₀',
          IsSiegelPoint F G T' i' ν' T₀' j' C' t' Ω' a' (q * x) ∧
            siegelModulus F G T' i' ν' T₀' j' a' = siegelModulus F G T i ν T₀ j a

end Langlands.Global
