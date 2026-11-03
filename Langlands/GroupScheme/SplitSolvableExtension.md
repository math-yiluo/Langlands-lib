# Pulling back and joining represented split-solvable series

This internal construction supports the algebraically closed solvable-group
series argument. It uses the published actual group-scheme pullbacks and the
existing `SplitSolvable.HasSeries` predicate. No new structural existence
theorem about solvable or unipotent groups is asserted.

For an actual homomorphism `q : G ⟶ Q`, subgroup map `j : H ⟶ Q`, and
`i : N ⟶ G` killed by `q`, `SubgroupPreimage.kernelInclusion` maps `N`
to the actual pullback of `q` and `j`. Its projections are `i` and the
zero homomorphism. If `i` is monomorphic, so is this lift. If `q` is an
fppf quotient with kernel represented by `i`, the projection of that
pullback onto `H` is an fppf quotient with kernel represented by the lift.
The proof checks kernel equality on every relative scheme test, and
uses base change for flatness, surjectivity and local finite presentation.

The composite-quotient lemma identifies the kernel of two successive
specified fppf quotients with the actual inverse image of the second
kernel. A smooth geometrically connected map has connected inverse
images of connected subgroups, by geometric connectedness under base
change and the open-map connectedness lemma.

`SplitSolvable.HasSeries.of_extension` joins a length-`n` series of a
represented kernel to a length-`m` quotient series, obtaining length
`n + m`. It retains smoothness and geometric connectedness of the quotient
map as explicit hypotheses. In the length-zero quotient case, all-test
triviality identifies the kernel representative with the entire source,
and series transport along this actual isomorphism applies. At a
successor, the proof pulls back the next subgroup, verifies its closedness,
smoothness, connectedness and normality, and uses the composite elementary
quotient before applying induction to the pullback projection.

These are internal consequences of the universal property of pullbacks,
the existing all-test kernel convention and Mathlib's geometric
connectedness results. They do not establish the existence of a
unipotent kernel, its split series, a represented torus quotient, or a
series for every smooth connected solvable group.
