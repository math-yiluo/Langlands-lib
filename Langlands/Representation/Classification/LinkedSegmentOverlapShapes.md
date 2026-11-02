# Block shapes of two overlapping segments

Author: Worker 1033.

This module fixes the combinatorial data of the overlapping case of Zelevinsky
1980, Proposition 4.6, step (2). It lives in the namespace
`Langlands.Classification.QuotientHom`. Step (2) of Zelevinsky's proof (Ze80
4.6, printed p. 186) takes the Jacquet module of `⟨Δ⟩ × ⟨Δ'⟩` along the shape
`γ = (deg Δ∪, deg Δ∩)`. The quotient it uses has the factor
`⟨Δ' \ Δ∩⟩ ⊗ ⟨Δ∩⟩` of the Jacquet module of `⟨Δ'⟩`. Below we write
`Δ' = init ∪ term`, so `term = Δ ∩ Δ'` and `init = Δ' \ Δ∩`. The three
blocks `(deg Δ, deg init, deg term)` are common to both refinements. The data
below make this concrete for `GL_n`. The choice of refinements and of the
common product is an internal construction.

## Coordinates of two-block shapes

- `index_zero_val`: the ambient coordinate of entry `a` of block `0` is `a`.
- `index_one_val`: if block `0` has size `s`, the ambient coordinate of entry
  `a` of block `1` is `s + a`.
- `blockIndex_val_eq_zero_iff`: a coordinate lies in block `0` exactly when it
  is smaller than the size of block `0`. The proof writes the coordinate as
  `B.index j b` and uses the published
  `CuspidalSupport.LeviAdmissibility.index_val` (see
  [LinkedSegmentSocleIdentityPiece](LinkedSegmentSocleIdentityPiece.md)). For
  `j ≠ 0`, the size of block `0` is one summand of the offset
  (`Finset.single_le_sum`).
- `blockIndex_le_of_length_one`: in a one-block shape all coordinates have the
  same block.
- `blockIndex_le_iff_of_length_two`: let block `0` of a two-block shape have
  size `s`. Then `blockIndex a ≤ blockIndex b` holds iff `a < s` or `s ≤ b`.

## The configuration

`OverlapConfig T n` packages:

- segments `Δ`, `Δ'` and `U`;
- a split point `q` with `0 < q < Δ'.length`;
- `hn : deg Δ + deg Δ' = n`;
- `hU : deg Δ + deg init = deg U`.

Here `init = Δ'.initial q hq` and `term = Δ'.terminal q hqm` (abbreviations
`O.init`, `O.term`). The structure itself does not say that `U` is the union
or that `term` is the intersection. Those facts are supplied separately by
`exists_overlap_split` in `LinkedSegmentOverlapSplit`. The degree identities
`degree_U`, `degree_Δ'` (from the published
`Segment.initial_degree_add_terminal_degree`), `degree_n` and `tgt_sum`
(`deg U + deg term = n`) follow by arithmetic.

The shapes are:

- `B = T.segmentShape ![Δ, Δ'] hn`, the source shape `(deg Δ, deg Δ')`;
- `C = T.segmentShape ![U, term] tgt_sum`, the target shape `(deg U, deg term)`;
- `unionShape = T.segmentShape ![Δ, init] hU`, the shape `(deg Δ, deg init)` of
  `GL(deg U)`.

The refinements at the identity permutation are:

- `S`, a refinement of `B`. Block `0` is kept whole (the published
  `CuspidalSupport.LeviAdmissibility.oneBlock`). Block `1` is split by the
  published `Δ'.socleSplitShape q hq hqm` into `(deg init, deg term)`.
- `R`, a refinement of `C`. Block `0` is split by `unionShape` and block `1` is
  kept whole.

`hS : IsIntersectionRefinement B C 1 S` and
`hR : IsIntersectionRefinement C B 1⁻¹ R` are proved with the published
`standardIntersections_of_comparisons`. It reduces each claim to comparing
block indices of coordinates within one outer block. Those comparisons follow
from `blockIndex_le_iff_of_length_two`, `index_zero_val`, `index_one_val` and
`omega`.

## The common product

`P = GL(deg Δ) × GL(deg init) × GL(deg term)`. The homomorphisms
`sourceCoords` and `targetCoords` read the three inner blocks off a product
of refined Levi factors. `φB` and `φC` compose them with the inverses of the
published `refinedLeviEquiv` for `(B, S)` and `(C, R)`.

`idx_Δ`, `idx_init` and `idx_term` show that each of the three inner blocks
sits at the same ambient coordinates in `(B, S)` and in `(C, R)`. The proofs
are coordinate arithmetic with `index_zero_val`, `index_one_val` and
`degree_U`. `coords_compat` then shows that refined Levi elements of `(B, S)`
and `(C, R)` with equal ambient matrices have equal images in `P`. It applies
`refinedLevi_entry_eq` entrywise to the three blocks.
