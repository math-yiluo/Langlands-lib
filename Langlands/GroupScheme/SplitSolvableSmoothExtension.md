# Split-solvable series through a smooth connected kernel

This internal derived unit joins represented Ga/Gm series along an actual
fppf quotient of affine group schemes over a field. It derives the smoothness
and geometric connectedness of the quotient map from a smooth connected
affine represented kernel. These map hypotheses were explicit in
`SplitSolvable.HasSeries.of_extension`.

First, `RelativeRoot.IsFppfQuotient.geometricallyConnected_of_connected_kernel`
identifies the given kernel representative with the actual kernel using
`IsFppfQuotient.kernelIso`. A connected finite-type group over a field is
geometrically connected. The proof transports this property along the kernel
isomorphism, then applies the actual-kernel theorem
`geometricallyConnected_of_geometricallyConnected_kernel`. This first result
requires a connected finite-type representative, without smoothness.

Next, `SplitSolvable.HasSeries.of_smooth_connected_extension` obtains
quasi-compactness of the quotient map from affineness of its source.
`IsFppfQuotient.smooth_of_smooth_kernel` gives smoothness of the map, and the
preceding result gives its geometric connectedness. The existing extension
lemma then joins a length-`n` kernel series and length-`m` quotient series into
a length-`n + m` series on the source.
`smoothConnectedExtensionSeries` packages this result as the exact proposition
`SmoothConnectedExtensionSeriesStatement.{u}`.

Finally,
`IsSplitSolvableGroupScheme.of_splitUnipotent_kernel_splitTorus_quotient`
uses a supplied Ga-series on the kernel and the split-torus Ga/Gm series on
the quotient. It retains the source's smoothness, affineness, connectedness
and geometric-point solvability as explicit hypotheses and returns the full
existing split-solvability predicate.

All series, subgroup, quotient and terminal-triviality predicates are the
existing all-test predicates. The construction uses the actual inverse-image
groups from the extension lemma. This unit asserts no existence of a
unipotent kernel or torus quotient for an arbitrary solvable group, and does
not prove `AlgebraicallyClosedSplitSolvableStatement`. Its provenance is the
imported kernel, geometric-connectedness, fppf-smoothness, series-extension
and split-torus proofs; no additional structural theorem is assumed.
