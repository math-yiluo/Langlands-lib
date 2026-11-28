# Compact split bases in the relative coroot chart

For a standard parabolic \(Q\), `relativeSplitVector` maps real coordinates
indexed by the simple roots outside its Levi to their linear combination of
projected simple coroots. The ambient fundamental weights outside the Levi
recover the coordinates. Conversely, in the intersection of the split
subspace of \(Q\) and the ambient coroot span, these coordinates reconstruct
every vector. The proof compares the logarithm in the given relative split
space with the projected coroot expression for the same positive split point.
The maximal torus embedding identifies the two torus points, so their
logarithms agree.

`relativeSplitClosedBase` implements the split cell of Delorme (7.26) by
weakening the strict lower root inequalities of `characteristicSplitShell`.
The upper weight inequalities at \(T+S\) are unchanged. The nonstrict root
constraints put every coordinate above the corresponding weight at \(T\).
The closed cell therefore lies in the compact coordinate box between the two
weight tuples.

`relativeSplitBaseChart` proves compactness and, for \(T\) in the ambient
coroot span, equality almost everywhere with the strict split shell in these
coordinates. A standard cocharacter for \(Q\), projected to the ambient
coroot span, has strictly positive values at every root outside \(Q\). It
witnesses that each of these root functionals on the split chart is nonzero.
The lower root walls are translates of the kernels of those functionals, so
they have Lebesgue measure zero. The proof uses the finite collection of
these walls to pass from the nonstrict inequalities to the strict ones
almost everywhere. This compares the bases of the ordinary and regularized
face integrals with respect to complementary coroot Lebesgue measure.

Source. P. Delorme, *On the spectral theorem of Langlands*, Advances in
Mathematics 426 (2023), 109107, §7, journal pp. 28–30, (7.23) and (7.26).
