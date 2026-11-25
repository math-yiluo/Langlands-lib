# The full star action on an actual type-D diagram

This internal module transports the elementary type-D Cartan symmetry results
to the full absolute Galois action on actual Tits index vertices. It works over
every field at arbitrary universe, with the supplied affine locally finite type
group scheme and its actual Tits index data. No local field or rank-one
assumption is needed for these action results.

`star_fixes_center_of_D` proves that every full Galois element fixes the vertex
with zero-based number `n - 3` whenever `n ≥ 4`.
`star_fixes_nonfork_of_D` proves that all vertices numbered `i` with
`i + 2 < n` are fixed whenever `n ≥ 5`.

`star_cases_of_D` proves that for `n ≥ 5` every full Galois element acts on the
entire numbered diagram either as identity or as `CartanDNumbering.forkSwap`.
If the full action is nontrivial, `starImagePair_of_D` proves its image is
exactly those two permutations. The same conclusions hold for `n ≥ 4` in
`star_cases_of_D_of_fixes_nonfork` and
`starImagePair_of_D_of_fixes_nonfork` when fixation of every nonfork vertex
is supplied explicitly.

The actual star action preserves the actual Cartan pairing. Transporting it
along the given numbering therefore gives a function preserving every entry
of `CartanMatrix.D n`. The imported combinatorial theorems fix the center and
nonfork vertices and classify the remaining global choice on the tips.
Nontriviality supplies a full Galois element moving an actual vertex; the
identity case is impossible for this element, so its action realizes the
fork swap on the entire diagram. This also shows that the swap is nonidentity,
as required by `StarImagePair`.

These results do not exclude trialitarian actions in rank four or impose any
arithmetic restriction on the rank or the distinguished subset.
