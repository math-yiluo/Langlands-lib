# Target-chart change for arbitrary bounded affinoid maps

Let `a` be an actual indexed affinoid atlas over a complete ultrametric normed
field. The ambient space and atlas index have independent universes. Given any
presented affinoid algebra `R` and a bounded algebra map `φ` from the algebra
of chart `i` to `R`, suppose its entire ambient spectrum image lies in another
original chart `j`. `changeMapChart` constructs an actual bounded algebra map
from the algebra of `j` to the unchanged algebra `R`.

The construction requires no domain representation for the image of `R`.
First, `originalChartRestriction_test_overlap` proves algebraic compatibility
on arbitrary affinoid tests into two common subcharts. Agreement over one
containing chart implies agreement over the other. Its proof factors the test
through the actual full intersection in the first chart, applies full-domain
uniqueness to recover both original test maps, and then composes the previously
proved full-domain overlap identity with that factor.

For any finite common-chart cover of a subset containing the entire image of
the test, `mapPullbackCover` constructs actual inverse-image quotients covering
the whole spectrum of `R`. Each local coefficient map is the second actual
pushout projection followed by an original chart restriction. The preceding
test-overlap result proves compatibility on every full-domain test of two
members of this source cover. `glueMapChartChange` applies the proved bounded
algebra-map descent theorem. Its local equation preserves the complete bounded
maps, including algebraic information that spectrum points need not detect.

`mapPullbackFamily_chart` follows from the original chart equations and the
actual pushout square. Coverage of the entire source spectrum and the exact
bounded descent equations then prove `glueMapChartChange_chart`.
`mapImageChartCover` constructs the requisite finite cover from compactness of
the actual test spectrum image and the original net intersection axiom.
`changeMapChart` uses this cover, and `changeMapChart_chart` identifies its
ambient point map with the original one at every point of the spectrum of `R`.

This is an internal construction from the actual atlas, its original
restrictions, full-domain intersections and inverse images, and bounded descent.
It makes no new literature attribution. Arbitrary finite positive polyradii,
closed quotient ideals, trivial valuations, nonreduced or zero quotients and
empty spectra are retained. Neither a greatest chart, directedness, saturation
nor a further gluing output is assumed.

The present unit establishes the constructed map and its exact local and
ambient equations. Independence from choices, coefficient naturality and
coherence of chart changes remain further results; they are not inferred from
the ambient point equation. General strong composition and analytic or
equivariant etale sites also remain further work.
