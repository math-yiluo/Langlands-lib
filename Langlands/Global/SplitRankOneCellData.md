# Rank-one cell data for a split rank-one parabolic line

Author: Worker 10.

This module starts from the hypotheses of
`SplitRankOneParabolicRationalOrbitHeightBoundStatement`. These are: a
connected reductive `G` over `F`, a maximal split torus `i : T ⟶ G` that is
also a maximal torus, a generic cocharacter `ν` with a single simple relative
root `α`, and a coordinate `j` whose exact line stabilizer is
`standardParabolic i ν ∅`. From these it builds the following data:

- the raising and lowering root maps `xp`, `xm`;
- the coroot `cor`;
- the open big cell `xm · T · xp`;
- the torus character `lam` of `e_j` and its coroot weight `k`;
- the integral relation `d • lam = eta|_T + b • α` with `d > 0` and
  `d * k = 2 * b`.

## Provenance

This is internal infrastructure for the split rank-one height bound
(`SplitRankOneAdelic.md`). It assembles published Library results, so the
mathematical input is theirs:

- the root datum (`rootDatumExistence`);
- the split rank-one root cell (`splitRankOneRootCell`);
- the line-character relation `d • lam = eta|_T + b • α`, from the published
  theorem
  `MatrixRepresentation.positiveRootRelation_of_exact_emptyStandardParabolic_stabilizer`
  in `Langlands/GroupScheme/Rational/RankOneStandardParabolicLineCharacter`.
  The provenance of this relation is the provenance recorded in that Library
  module: an internal derived construction from earlier proved positivity,
  parabolic and rational-character results. It is not taken from a
  literature source.

Springer, *Reduction theory over global fields* (1994), §§3.2–3.3, is only
the context for the split rank-one case: the reduction to rank one and the
classification of split rank-one groups (printed pp. 214–215). It is not
the source of the line-character relation, and this module does not follow
it.

## Definitions

`CellData ρ j i α` is a structure (data, not a proposition) with these fields:

- `xp`, `xm : 𝔾ₐ ⟶ G`: the raising and lowering root maps.
- `cor : cocharacterLattice T`: the coroot.
- `lam : characterLattice T`: the torus character of the line through `e_j`.
- `k : ℕ`: the coroot weight of that line.
- `d b : ℕ` and `eta : rationalCharacters G`: the line-character relation.
- `hyp : CellHyp ρ j i xp xm cor α lam k` (see `SplitRankOneCellPoints.md`).
- `openCell`: the triple multiplication `xm × T × xp → G` is an open
  immersion.
- `pairing_root : ⟨α, cor⟩ = 2`.
- `d_pos : 0 < d`.
- `rel : d • lam = torusCharacterRestrict i eta + b • α`.
- `dk : d * k = 2 * b`.

## Results

- `not_linearIndependent_of_toRat_mem_span`: on a split torus, take a
  character `β` whose rationalization lies on the rational line of `α`. Then
  `![α, β]` is not `ℤ`-linearly independent.
- `roots_pairwise_dependent_of_simpleRelativeRoots`: when the simple relative
  roots are `{α}`, any two roots are integrally dependent. The proof uses
  `relativeRootSpan_eq_span_singleton_of_simpleRelativeRoots` together with
  `RootReducedness.not_linearIndependent_of_not_linearIndependent`. This is
  the hypothesis that `splitRankOneRootCell` requires.
- `latticePairing_torusCharacterRestrict_coroot`: the restriction to `T` of a
  rational character of `G` pairs to zero with every coroot. The Weyl
  reflection `s_r` comes from a normalizer point, and it fixes restricted
  rational characters (`weylAction_torusCharacterRestrict`). So
  `⟨η|_T, r^∨⟩ • r = 0`, and the torus has no torsion.
- `nonempty_cellData` (for `F` infinite and `G` affine over `F`): under the
  hypotheses listed at the top, `Nonempty (CellData ρ j i α)`. The proof:
  - `xp` fixes `e_j`. Its image lies in the root subgroup of `α`
    (`RankOneRootCellRelation.comp_mem_rootSubgroup`). That subgroup lies in
    `standardParabolic i ν ∅`
    (`RelativeRoot.subgroup_le_standardParabolic_empty`), which stabilizes
    the line. A unipotent vector group then fixes `e_j`
    (`isFixedVector_single_of_isUnipotent`).
  - `lam` is the coordinate-line character (`torusCoordinateLineCharacter`).
  - The weight satisfies `0 ≤ ⟨lam, cor⟩` (`CellHyp.pairing_nonneg`), so
    `k` is its natural-number value.
  - Pairing `rel` with `cor` gives `d * k = 2 * b`, using
    `latticePairing_torusCharacterRestrict_coroot` and `⟨α, cor⟩ = 2`.
