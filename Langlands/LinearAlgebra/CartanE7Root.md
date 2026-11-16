# E₇ rigidity and an actual root certificate

This internal finite unit defines the integer coefficient vector
`(2, 2, 3, 4, 3, 2, 1)` and proves two facts about Mathlib's numbered E₇
Cartan matrix.

Every self-map preserving all Cartan entries fixes every vertex. Its
injectivity follows from the diagonal entries; finiteness gives
bijectivity. Five adjacency walk refinements from the constant color one
give the vectors

- `(1, 1, 2, 3, 2, 2, 1)`;
- `(2, 3, 4, 5, 5, 3, 2)`;
- `(4, 5, 7, 12, 8, 7, 3)`;
- `(7, 12, 16, 20, 19, 11, 7)`;
- `(16, 20, 27, 47, 31, 26, 11)`.

Each refinement is invariant under the given map. The last vector has
distinct entries, so invariance forces the identity.

For any family of seven actual roots with these Cartan pairings, the
coefficient vector represents an actual root. Starting with the seventh
selected root, sixteen applications of the actual-root reflection theorem
use the vertex sequence

`5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0`.

Every intermediate vector is explicit in Lean. Ordinary kernel-checked
`decide` verifies the finite walk counts, the last vector's injectivity and
each integer coefficient reflection equality. No independence of the
selected roots is required. The actual-root conclusion asserts existence
of the stated root, without claiming maximality among positive roots.
Both results are internal deductions from the Cartan entries and the
root-datum reflection formula, with no external classification theorem.
