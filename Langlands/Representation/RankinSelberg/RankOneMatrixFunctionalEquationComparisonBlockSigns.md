# Coordinate signs for actual rank-one blocks

This internal helper defines the alternating row map
`(S_j X)_(i,b) = (-1)^(i+1) X_(i,b)` with zero-based row indices.
It proves, for the actual rank-transported `blockMatrixAt`,
`m_j(g,X) E = m_j(-g,-X)` and `T m_j(g,X) T = m_j(g,S_j X)`.

These algebraic identities hold over every field, including all rank
transports `n = 0 + (j + k + 1)` used by `blockMatrixAt`. Their proofs use the
published entry formula, distinguish the first column from the identity
columns, normalize the unique scalar-column index, and cancel pairs of
powers of `-1`. The row map is an involution.

For a locally compact, Hausdorff, second countable topological field with
its Borel measurable space, the file packages the row map as a measurable
equivalence. With a supplied additive Haar measure whose underlying measure
is sigma finite, both the row map and rectangular negation preserve exactly
`rectangularMeasure ν j 1`. The proof reduces every scalar power of `-1`
to either the identity or additive negation, uses Haar invariance under
negation, and applies the product-measure theorem twice. Consequently the
row substitution preserves the total complex Bochner integral for every
integrand, without an integrability premise.

The actual quotient sign map is right translation by `-1` on
`N₁ \ GL₁`; on a represented coset it sends `[g]` to `[-g]`.
Every supplied compatible quotient measure is preserved because right
invariance is part of its compatibility property. When this measure is
s-finite, its product with the supplied rectangular measure is preserved by
the simultaneous scalar and rectangular negation used in `m_j(g,X) E`.
The relevant group, subgroup and quotient measurable structures are
explicit parameters in Lean, with the stated Borel assumptions.

The provenance is internal derivation over the published matrices and
measure definitions, using Mathlib's finite product and Haar theorems.
The file supplies coordinate substitutions for the signed-to-unsigned
comparison; it does not assert the weighted extraction or gamma equation.
