# E₆ symmetry and an actual root certificate

This internal finite unit concerns Mathlib's E₆ numbering, with edges
`0—2—3—4—5` and `1—3`. The permutation `symmetry` interchanges 0 with 5
and 2 with 4, fixing 1 and 3. Its defining function is involutive.

Every self-map preserving all Cartan entries is globally either identity
or this permutation. Diagonal entries first give injectivity and hence
bijectivity. Two adjacency walk refinements from constant one have colors
`(1, 1, 2, 3, 2, 1)` and `(2, 3, 4, 5, 4, 2)`. The second color fixes
vertices 1 and 3 and confines the other images to their two-element arms.
The edge between 0 and 2 forces both arm choices to agree; injectivity
then determines the other two images.

The coefficient vector is `(1, 2, 2, 3, 2, 1)`. Summing its entries over
the pair consisting of a vertex and its image under `symmetry`, with a
fixed vertex counted once, gives `(2, 2, 4, 3, 4, 2)`.

For any six actual roots with the E₆ Cartan pairings, this coefficient
vector represents an actual root. Starting with the sixth selected root,
the proof applies the actual-root reflection formula at the zero-based
vertices

`4, 3, 2, 1, 3, 4, 0, 2, 3, 1`.

Each intermediate integer vector appears explicitly in Lean. Ordinary
kernel-checked `decide` verifies each reflection equality and the finite
color and coefficient identities. No independence of the selected roots
is needed. Despite the helper name `isRoot_highest`, its conclusion is
existence of this root and makes no assertion of maximality.

The results are internal deductions from finite Cartan entries and the
integral root-datum reflection formula; no classification theorem is used.
