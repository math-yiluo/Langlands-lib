# Proof: the Isomorphism Theorem in semisimple rank at most one, common torus

Authors: Worker 239 and Worker 1388.

Module `Langlands.GroupScheme.Reductive.SplitRankOneIsomorphismProof`. It proves the
published statement

`splitRankOneCommonTorusIsomorphism : SplitRankOneCommonTorusIsomorphismStatement.{u}`

of `Reductive.SplitRankOneIsomorphismStatement` at its original universe `u`, with no
hypotheses: two connected reductive groups over a field with a common split maximal torus
`T`, the same roots and the same coroots, of semisimple rank at most one, are isomorphic
by an isomorphism that is the identity on `T`.

## The implemented proof

The proof is one line,
`splitRankOneCommonTorusIsomorphism_of_rootCell splitRankOneRootCell`. It applies the
reduction of `SplitRankOneRootCellReduction` to the root-cell theorem of
`SplitRankOneRootCellProof`. The modules of the proof are:

- `Reductive.SplitRankOneRootCellStatement` (Worker 1388): the statement
  `SplitRankOneRootCellStatement` (root groups `xp`, `xm`, the open cell, the cell
  criterion `1 + XY` a unit, and the rank-one relation).
- `Reductive.SplitRankOneRootCellReduction` (Worker 1388):
  `splitRankOneCommonTorusIsomorphism_of_rootCell`. If `J₁` is empty, the rank-zero
  case `exists_iso_of_roots_eq_empty` of `Reductive.SplitRankZeroIsomorphism`
  (Worker 239) applies. Otherwise the root cells of the two groups for the same root and
  coroot have the same multiplication of cell points, and the gluing criterion of
  `OpenCellGluing` (Worker 1388) gives the isomorphism.
- `Reductive.RankOneCellData` (Worker 239): the root groups as dynamic unipotent subgroups,
  isomorphic to `𝔾ₐ`, and the open cell (`rankOne_exists_rootCell`), from the Library
  theorems `dynamicCentralizerReductive`, `rankOnePositiveRootUniqueness` and
  `splitRootLieLine`.
- `Reductive.RankOneRootCellRelation` and `Reductive.RankOneRootCellWeyl` (Worker 239):
  the rank-one relation and the cell criterion over algebraically closed points, through
  the Weyl point `n` normalizing `T`, for `xm` rescaled by a unit `β` of `k`.
- `Reductive.SplitRankOneRootCellUniversal` (Worker 1388): descent of the relation and the
  cell criterion from algebraically closed points to all test schemes.
- `Reductive.SplitRankOneRootCellProof` (Worker 239): `splitRankOneRootCell`, which
  assembles the last four modules.

`SplitRankOneRootCellStatement`, `SplitRankOneRootCellReduction`, `OpenCellGluing` and
`SplitRankZeroIsomorphism` are published in the Library; the other modules are part of
this candidate. Each has its own
Markdown with the details.

## Provenance

The statement is Milne, *Algebraic Groups* (2017), Proposition 23.14 (printed p.489) and
the paragraph before it, in the isomorphism case together with Proposition 23.5 (printed
p.485), for two groups with a common split maximal torus (literature
`milne-2017-algebraic-groups`); see the Markdown of the statement. The proof does not
follow Milne, who classifies the groups of semisimple rank one. It follows the root-group
and open-cell approach of Conrad, *Reductive group schemes*, Theorems 4.1.4 and 4.2.6
(literature `conrad-2014-reductive-group-schemes`), as described in the Markdown of
`SplitRankOneRootCellReduction` and `RankOneRootCellWeyl`.
