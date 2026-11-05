# Actual projective frame fibres and their degree-one bundles

This internal derived construction uses the actual projective frame bundle
and its Cartesian charts. The base scheme and coefficient module are
arbitrary in a common universe. The module is assumed locally free of
the displayed rank `n + 1`.

If a map from a scheme `T` to the base factors through a frame-bearing
open `U`, the map from relative projective space over `T` to the frame
bundle is the relative projective base-change map followed by the
original frame chart. Pasting the two existing Cartesian squares proves
that this identifies projective space over `T` with the actual pullback
of the frame bundle. The two projection identities specify the
isomorphism. The global degree-one bundle pulls back to the usual
degree-one bundle, by the chart comparison and the existing relative
projective base-change comparison.

For a point `s` in `U`, the original map from its residue field spectrum
factors through `U` by the open-immersion lifting property. This uses the
actual residue field of the original base. The preceding Cartesian
construction supplies `fibreChartIso`, an isomorphism from projective
space over that residue field to the whole actual fibre of the frame
bundle. Its projection to the residue spectrum is the usual projective
structure map. Pullback along the isomorphism takes the restriction of
the global degree-one bundle to the usual degree-one bundle.

Fixed-rank local freeness supplies a frame open containing every point.
Choosing one gives `fibreProjectiveIso` and `fibreProjectiveTwistIso`
without another frame-existence premise. The isomorphism depends on this
choice of frame; no independence from it is asserted.

All these results follow from already implemented projective chart
gluing, relative projective base change, and line-bundle pullback
functoriality. They do not assert that any direct-image base-change map
is invertible, identify a full fibre evaluation morphism, prove
generation or very ampleness, or prove moduli representability.
