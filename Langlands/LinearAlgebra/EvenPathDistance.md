# Distance from the middle pair of an even path

Provenance: derived. This module contains the unchanged
`Langlands.GroupScheme.SplitPinning.middleDistance` definition extracted from
`Langlands.GroupScheme.Rational.EvenChainPatternProducts`. Its namespace is
preserved for existing users. The root-datum geometry and group-scheme product
interfaces both import this arithmetic definition.

`middleDistance m i` is `m - 1 - i` if `i + 1 < m`, and `i - m` otherwise,
with natural subtraction. For `m > 0` and `i < 2*m` it gives the distance from
the middle pair `{m-1,m}`; both middle positions have distance zero. It is
also defined outside these bounds.

The indexing convention comes from the products before Theorem 9.11 in
Robert Steinberg, *Regular elements of semi-simple algebraic groups*,
printed p.74 (PDF p.27), source
`steinberg-1965-regular-elements-semisimple-groups`, SHA-256
`bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
The source's middle positions `m,m+1` become the zero-based positions
`m-1,m`. This module introduces no existence or ordering assertion.
