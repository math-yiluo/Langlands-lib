# Berkovich's Proposition 6.1 for strong maps into a chart

This module proves a form of Proposition 6.1 of Berkovich, *Vanishing
cycles for formal schemes* (Invent. Math. 115, 1994), for strong maps
of saturated atlas presentations. In Berkovich's statement, a finite set
of test triples on the target is controlled by finitely many functions:
maps that are close on these functions satisfy the test relations. Here
both maps send every source chart into one fixed chart `c` of the
target, and closeness is measured by the pullbacks of finitely many
functions on `c`, uniformly at every spectrum point of every source
chart. The conclusion is the Library's relation `StrongNear τ a b`.

`exists_finset_charts_cover_inter` covers the intersection of two
charts `d` and `c` of a Hausdorff space by finitely many charts lying
in both. The proof uses that the range of `d` is compact and hence
closed. Its preimage in the subspace `c` is then compact and is covered
by finitely many charts of that subspace.

`exists_subchart_transfer` handles one chart `R` lying in `c` and in
the domain `U` of a test triple. The restriction from `c` to `R`
represents an affinoid domain of `O(c)`. The Library's test transfer
for such domains, `Domain.hasSpectralTestTransfer`, gives finitely many
functions on `c` and a bound. Suppose `a` sends a source chart `k` into
`R` and both maps send `k` into `c`, with pullbacks close on these
functions. Then `b` also sends `k` into `R`, and the pullbacks of the
restriction of the test function to `R` differ by at most the test
bound. The proof identifies the pullback of `b` at `(k, R)` with the
factorization given by the transfer, by uniqueness of factorizations
through a represented domain.

`exists_chart_tests_strongNear` is the proposition for one test triple
`τ` with domain `U`. Cover `U ∩ c` by finitely many charts `R` as above
and collect the functions and the least bound from
`exists_subchart_transfer` for each `R`. Let a source point be sent
into `U` by `a`. Its image lies in some `R`, and a source subchart
around the point is sent into `R` by `a`
(`exists_subchart_image_subset`). The transfer shows that `b` sends this
subchart into `R` as well. This gives equal preimages of `U`, applied
in both directions, and test pieces covering the preimage. On an
arbitrary test piece `i` and a spectrum point `p` of `O(i)`, choose such
a subchart `k` around the image point of `p` and a point `p'` of `O(k)`
restricting to `p` (`exists_restriction_comap_eq`). Both pullbacks of
the test function, restricted from `i` to `k`, are pullbacks at `(k, R)`
of its restriction to `R`. The transfer bound at `p'` is the required
bound at `p`.

`exists_chart_tests_strongNear_finset` treats finitely many test
triples at once, by taking unions of the functions and minima of the
bounds. `exists_globalChart_tests_strongNear` specializes to a source
with a chart `P` whose range is the whole space. Closeness of the
pullbacks at `P` alone suffices, since restriction from `P` to any
chart does not increase spectral values.
