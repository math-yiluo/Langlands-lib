# Actual field roots of complementary-torus centralizers

For the actual component-indexed centralizers of an
`AffineSimplyConnectedPinnedModel`, this internal module identifies the roots
on every supplied field-valued fibre. With respect to the full normalized
coordinate torus, an ambient root occurs in the centralizer precisely when its
integral Cartan component is the selected component.

The proof retains the actual source and target torus isomorphisms during
base change. The complementary simple-coroot inclusion commutes with any
scheme base change by `splitTorus.exponentHom_baseChange`. Consequently the
normalized complementary torus on a specified field is its integral torus
inclusion followed by the normalized full maximal torus. The base change of
the relative centralizer represents its all-test centralizer.

The published field theorem for roots of a represented split-torus
centralizer identifies its roots with ambient roots restricting trivially to
the complementary torus. The exact character pullback formula reduces this
to the integer restriction map. Over the supplied field, fixed-exponent
characters detect those integer coordinates. The component restriction
criterion from `SimplyConnectedCorootSubtori` completes the comparison.

These are derived consequences of the existing coordinate, centralizer and
root-support constructions, motivated by Conrad, *Reductive group schemes*
(2014), Proposition 6.4.4, pp.232–233. This module compares the centralizer
roots; it does not assert almost simplicity or the product isomorphism for
the relative derived groups.
