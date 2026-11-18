# Split rank two for isotropic Cayley automorphism group schemes

Authors: Worker 118, with Worker 622 (module
`Langlands.GroupScheme.Composition.CayleyPeirceExistence`).

This module proves the published proposition
`Langlands.GroupScheme.IsotropicCayleyAutomorphismRankStatement`
(module
`Langlands.GroupScheme.Composition.IsotropicCayleyAutomorphismRankStatement`)
at every universe level `u`.

## Main results

- `CayleyDatum.splitRank_eq_two_of_peirceFrame (hrep) (D : c.PeirceFrame) :
  splitRank H = 2`. Let `c : CayleyDatum K` and
  `iH : H ⟶ GL₈` with `hrep : c.IsAutomorphismRepresentation iH`, and
  suppose `c` admits a Peirce frame `D`. Then the split rank of `H` is two.
- **`isotropicCayleyAutomorphismRank :
  IsotropicCayleyAutomorphismRankStatement.{u}`**.

## Proof

Upper bound: `splitRank_le_two hrep` (module
`Langlands.GroupScheme.Composition.CayleyTorusUpperBound`). Every closed
split torus `𝔾ₘ^I → H` grades the algebra by `ℤ^I`, with degrees
generating `ℤ^I`. Such a grading forces `|I| ≤ 2` (`Grading.card_le_two`
in `CayleyGrading`).

Lower bound: `PeirceFrame.exists_grading` (module
`Langlands.GroupScheme.Composition.CayleyPeirceFrame`) turns the Peirce
frame into a grading by `ℤ²` (indexed by `ULift (Fin 2)`) whose degrees
generate `ℤ²`. `Grading.card_le_splitRank hrep` (module
`Langlands.GroupScheme.Composition.CayleyGradingTorus`) turns that grading
into a closed split torus of dimension two in `H`. So
`2 ≤ splitRank H`.

Main theorem: given a nonzero `x` with `N(x) = 0`,
`exists_norm_eq_zero_trace_eq_one` produces `e` with `N(e) = 0` and
`T(e) = 1`. Worker 622's `exists_peirceFrame` produces three vectors
`u a` in the Peirce space `U(e)` and three vectors `v a` in `U(1 - e)`
with `b(u a, v b) = δ_ab`. Together these form a `PeirceFrame`, and
`splitRank_eq_two_of_peirceFrame` concludes.

## Module structure

All helper modules are new and live in
`Langlands/GroupScheme/Composition/`. Each has its own Markdown.

- `CayleyIdentities`: polar form, trace, composition identities.
- `CayleyGrading`: gradings and the rank bound `card_le_two`.
- `CayleyTorusUpperBound`: weight grading of a split torus, and
  `splitRank_le_two`.
- `CayleyGradingTorus`: split torus from a grading, and
  `card_le_splitRank`.
- `CayleyFrameGrading`: gradings from weighted self-dual frames.
- `CayleyPeirceExistence` (Worker 622): existence of the dual triples
  `u`, `v`.
- `CayleyPeirceFrame`: the isotropic idempotent, the Peirce multiplication
  table, the weighted frame, and the `ℤ²`-grading.

## Provenance

The statement's Markdown describes the literature route through Knus,
Merkurjev, Rost and Tignol, *The Book of Involutions*: Theorem 33.17,
Theorem 33.19, Proposition 33.23, the discussion on printed p.462, and
Theorem 25.14. That route identifies an isotropic Cayley algebra with the
split model and its automorphism group with split `G₂`. The Lean proof
takes a different, self-contained route. It never constructs an algebra
isomorphism to a split model and never uses a classification of
composition algebras or of reductive groups. The upper bound is a
combinatorial argument on weight gradings. It uses only the composition
identities (KMRT Section 33.B), the Library's split-torus weight
decomposition (`Langlands.GroupScheme.Torus.RingRepresentationWeights`),
and `dim = 8`. The lower bound is an explicit two-dimensional torus
acting through the Peirce decomposition of an isotropic idempotent. It is
lifted through `iH` by the all-test automorphism hypothesis and shown
closed with the Library's `IsTorus.isClosedSubgroup_of_mono`. The proof
works over every field, in every characteristic, as the statement
requires. It does not use any local-field results, Tits indices, or
Kneser–Tits.
