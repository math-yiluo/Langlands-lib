# Consecutive triple merges

Author: Worker 19.

This internal finite-block construction merges three consecutive slots into
one block while retaining all outside blocks and their order. The inner
refinement numbers the original blocks and gives their exact standard
matrix coordinates. It makes no assertion about representation structure
or a Jacquet transfer.

The merged rank is the sum of exactly the original ranks selected by the
consecutive nested label bijection. That bijection has value
`m + k + (if j < m then 2 else 0)`, with three inner slots at `j` and one
elsewhere. Positivity follows from positivity of all original ranks, and
the total-rank identity follows by summing over this bijection.

`tripleMerge` has `B.length - 2` blocks. `tripleMergeIndex` is its selected
slot `j`. The rank at that slot is the sum of the original ranks at
`j`, `j + 1`, and `j + 2`. Each outside slot `m` has the original rank at
`m + (if j < m then 2 else 0)`.

`tripleRefinement` has three inner blocks at the merged slot and a
singleton inner block everywhere else. `tripleBlockEquiv` identifies all
outer/inner labels with the original labels and has the explicit value
formula above. `tripleBlock_size` gives literal rank compatibility.
`tripleBlockEquiv_lt_iff` proves that the original labels have the
lexicographic outer/inner order. Arithmetic case distinctions handle
the three-inner versus one-inner bounds.

`triple_index` reuses the published `index_index_eq_of_lex`: nested
standard coordinates equal the original standard coordinates, with the
proved rank-equality cast in the forward direction. That theorem
constructs the nested coordinate self-map of `Fin n`, proves it strictly
increasing from the block and within-block orders, and uses uniqueness of
an increasing self-map of a finite ordinal. The imported proof was read
at declaration level; it introduces no permutation of ambient coordinates.

The two local swaps are parametrized by a natural number `δ ≤ 1`:
`δ = 0` swaps `j,j + 1`, and `δ = 1` swaps `j + 1,j + 2`.
`tripleMergeSize_permute_adjacentSwap` proves that either swap preserves
every coarse rank. On the merged block this is commutativity of addition
for the corresponding three summands. Outside it, the consecutive label
formula and the singleton bound show that the original label is fixed by
the swap. `tripleMerge_permute_adjacentSwap` consequently proves literal
equality of the two coarse shape structures.

`tripleSwapRefinement` is defined directly over the same original coarse
shape. Its inner counts remain three or one, and its sizes are the original
sizes precomposed with the selected adjacent swap. The preceding sum
identity is its total-rank proof; positivity is inherited from the
original ranks. `tripleSwapBlockEquiv` retains exactly the same
consecutive positional numbering, now for the permuted original shape.
`tripleSwapBlock_size` and `tripleSwapBlockEquiv_lt_iff` prove its rank and
order compatibility. `tripleSwap_index` gives the corresponding exact
standard-coordinate identity. Each outside singleton refinement equals
the original singleton refinement by `tripleSwapRefinement_of_ne`.
The merged size formula records the swapped original label at `j + k`.

There is no equality or distinctness assumption on any of the original
ranks; all outside ranks are retained. In particular, this construction
does not presuppose the equal-rank consequence of the host's cuspidal
class hypotheses. Applying an ordered Jacquet extraction or return
theorem to these data is subsequent representation-theoretic work.

## Dependency audit

The provenance is internal finite arithmetic and the existing positive
ordered-block definitions. The sole direct import is
`Group.GL.AdjacentMergeShape`. A recursive traversal over Library base
`125fca1a70e8f89af98a36c8565617cd68f73be5` contains 52 project modules
including this one; `Classification.Supercuspidal` is the only
classification-named module in that inventory.

The actual used dependency bodies are the positive block-shape data,
the consecutive finite Sigma numbering, finite-sum reindexing,
`BlockShape.ext_of_size`, `BlockShape.permute`, `BlockShape.adjacentSwap`,
and `BlockShape.index_index_eq_of_lex`. `permute` precomposes the size
family and obtains the sum by its actual finite label equivalence.
`adjacentSwap` is the existing transposition of the two specified
finite labels. `ext_of_size` identifies the structures by equal length
and equal size functions, with proof irrelevance for their positivity
and sum fields. The coordinate theorem uses only monotonicity of the
consecutive block and within-block index functions and the finite ordinal
identity described above.

Thus the imported supercuspidal definitions supply no representation
assertion to the implemented proof. No geometric-lemma calculation,
Jacquet theorem, support decomposition, quotient coverage or
classification result is used. The construction is directly and
transitively independent of the eight classification tasks excluded by
the host contract and their proof successors.
