# Symmetries of the numbered Cartan matrix of type D

This internal combinatorial unit classifies functions preserving every entry
of Mathlib's type-D Cartan matrix. `forkSwap n hn` names the permutation
interchanging the zero-based vertices `n - 2` and `n - 1`, with `hn : 2 ≤ n`.
The diagonal entry `2` first implies
injectivity. For rank at least four, the vertex numbered `n - 3` in zero-based
notation is the unique vertex with three distinct neighbors and is therefore
fixed by every such function.

For rank at least five the neighbor numbered `n - 4` is fixed as well. Its
image is adjacent to the fixed center and has two distinct neighbors, which
rules out both short fork tips. Descending induction along the remaining
chain fixes every vertex outside the two fork tips. Injectivity then forces
one global choice: both tips fixed, or both interchanged.

`eq_id_or_swap_of_preserves` states this classification for every rank at
least five, and `eq_id_or_forkSwap_of_preserves` states it with the named
permutation. `eq_id_or_swap_of_fixes_nonfork` gives the same conclusion for
rank at least four when fixation of the nonfork vertices is supplied.
`fixes_center` also applies to rank four, retaining the possibility that its
three arms are permuted. No arithmetic or group classification is used.
