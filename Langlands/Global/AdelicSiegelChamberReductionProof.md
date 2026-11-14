# The chamber form of Springer's fundamental set theorem

Author: Worker 5269.

This module proves the Library proposition
`Langlands.Global.AdelicSiegelFactors.AdelicSiegelChamberReductionStatement`
(module `Langlands.Global.AdelicSiegelChamberReduction`). This is the chamber form of the
fundamental-set property (F) in T. A. Springer, *Reduction theory over global fields*
(1994), §2.1, printed p.212 (registered source `springer-1994-reduction-global-fields`).

## Statement

The theorem is

`theorem adelicSiegelChamberReduction : AdelicSiegelChamberReductionStatement.{u}`

in the namespace `Langlands.Global.AdelicSiegelFactors`. It has no hypotheses and its type
is exactly the target proposition, at an arbitrary universe `u`.

Unfolded, it says the following. Fix:

- a number field `F : Type u`;
- a group scheme `G` over `Spec F` with `IsAffineHom G.X.hom`,
  `LocallyOfFiniteType G.X.hom` and `IsConnectedReductive G`;
- data `T, i, ν, T₀, j` with `IsSiegelAlgebraicSetup F G T i ν T₀ j`;
- a subgroup `K` of `AdelicGroupPoints F G` with
  `IsParabolicIwasawaCompact F G (Standard.parabolicScheme i ν ∅)
  (Standard.parabolicHom i ν ∅) K`.

Then there is a threshold `t : ℝ≥0ˣ` with the following property. For every `g` in
`normOneSubgroup F G` there exist:

- a principal rational point `q : RationalGroupPoints F G`;
- `n` in the adelic points of `Standard.unipotentScheme i ν ∅`;
- `m` in `normOneSubgroup F (Standard.leviScheme i ν ∅)`;
- `a` in `PositiveRealTorus.intrinsicSubgroup F T₀` lying in the weak chamber
  `PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t`;
- `k ∈ K`,

such that the unipotent image of `n`, times the Levi image of `m`, times
`positiveMap F G T i T₀ j a`, times `k`, equals `rational F G q * g`.

The theorem covers arbitrary number fields, nonsplit and anisotropic groups, and every
subgroup `K` satisfying the Iwasawa predicate. When there are no simple relative roots, the
chamber condition is vacuous.

## Proof

The proof is a single application of two published Library theorems:

`adelicSiegelChamberReduction_of_rankOne_height rankOneParabolicRationalOrbitHeightBound`.

1. `Langlands.Global.AdelicSiegelFactors.adelicSiegelChamberReduction_of_rankOne_height`
   (module `Langlands.Global.AdelicChamberFromRankOneHeight`) has the type
   `RankOneParabolicRationalOrbitHeightBoundStatement.{u} →
   AdelicSiegelChamberReductionStatement.{u}`. This is the reduction of the chamber
   statement to the semisimple rank-one case. Its module proves the factorization of
   every norm-one point of the minimal parabolic `P(𝔸_F)` as `n m a`
   (`IsSiegelAlgebraicSetup.hasMinimalParabolicNormFactors`). It combines this
   factorization with the given Iwasawa compact `K`. For each of the finitely many
   simple relative roots, it applies the rank-one height bound to the maximal standard
   parabolic obtained by deleting that root. This bounds the torus factor `a` from
   below and gives one chamber threshold `t`
   (`hasWeakChamberReduction_of_rankOne_height`).
2. `Langlands.Global.RepresentationGrowth.rankOneParabolicRationalOrbitHeightBound`
   (module `Langlands.Global.AdelicRankOneOrbitHeightBoundProof`) proves
   `RankOneParabolicRationalOrbitHeightBoundStatement.{u}` with no hypotheses. This is
   Springer's §3.6 estimate (printed pp.215–216). It assembles the split fundamental-set
   theorem, the split overlap estimate, the Galois overlap matching and the Galois twisting
   of a split Borel pair, each discharged by a published Library proof.

Applying the first theorem to the second gives the target. The only work done in this
module is that application. The theorem uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
