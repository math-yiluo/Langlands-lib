# Jacquet nonvanishing for inhomogeneous level-zero types in standard coordinates

Module `Langlands.BushnellKutzko.SplitTypeJacquet.StandardJacquet`. Let `F` be a nonarchimedean
local field and `n = m + 1`.

- `J1Open blk` is `J1 F blk` as an open subgroup: it contains the principal congruence subgroup
  of level one, which is open. It is compact (`isCompact_J1Open`) as a closed subset of the
  compact group `GL_n(𝔬_F)`.
- `exists_parabolicIntertwiner`: an intertwiner from `stdType E` into a representation `π` takes
  values fixed by the principal congruence subgroup and is equivariant for the parabolic over
  `k_F` acting through `descended π`; `stdType_intertwiner_of_parabolic` is the converse
  construction.
- `standard_jacquet`: let `π` be admissible and let `E` have two different block labels. If
  there is a nonzero intertwiner from `stdType E` into `π`, then there are a block shape `B` with
  `B.parabolic F ≠ ⊤` and `g` such that `Jacquet.Coinvariants π (B.conjugateUnipotent g)` is not a
  subsingleton.

Proof of `standard_jacquet`. Reorder the blocks of `E` by `exists_permute_separated` to a datum
`E'` with a cut `j`, `0 < j` and `j` less than the number of blocks, such that no block before the
cut carries the label of a block after it. The fixed vectors of the
principal congruence subgroup form a finite-dimensional representation of `GL_n(k_F)` by
admissibility; a finite-dimensional model is `FiniteRep.ofRepresentation`. By
`finrank_parabolicHom_eq_of_labels_eq`, the given intertwiner yields a nonzero parabolic
intertwiner for `E'`, hence a nonzero intertwiner from `stdType E'`. With `stdType_test`,
`not_subsingleton_coinvariants_coarseN` gives a nonzero Jacquet module along the coarse corner of
`E'`. By `conjugateUnipotent_le_coarseN` and `not_subsingleton_coinvariants_of_le` it is nonzero
along a conjugate of the unipotent radical of the proper two-block shape `(b, n - b)`
(`cutShape_parabolic_ne_top`).

In standard coordinates, this is the existential Jacquet nonvanishing consequence of C. J.
Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
(8.3.3), printed p. 291 (PDF p. 303), at level zero and for admissible smooth representations. The
theorem of the source says more. It takes a parabolic subgroup `P` subordinate to the given order
and minimal for this property and shows that the Jacquet module along the unipotent radical of `P`
contains the Levi representation `ϑ_U`. Neither statement is proved here. The proof here reorders
the cuspidal factors inside the finite group `GL_n(k_F)` instead of using the associated split
types of (8.3.4)–(8.3.5).
