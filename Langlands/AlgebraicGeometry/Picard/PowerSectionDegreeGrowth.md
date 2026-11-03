# Increasing section degrees without changing generation opens

This internal construction raises sections of an actual line bundle to
positive powers, using the tensor-power multiplication isomorphism to
identify the result with a section of the specified actual tensor power.

`LineBundle.multiplySectionDegree` sends a section of the `n`-th power
to a section of the `(n * k)`-th power. For positive `k`, its whole
generation open equals the original section's generation open. This is
the published generation-locus theorem for positive section powers,
transported along `tensorPowMulIso`.

`LineBundle.exists_sections_above_degree` applies this construction
simultaneously to a family of sections in one positive degree `n`.
Given a threshold `N`, it uses multiplier `N + 1` and common degree
`n * (N + 1)`, which is positive and at least `N`. Every generation
open is unchanged. The family may have arbitrary cardinality. In
particular, an affine section cover remains affine and remains a cover.

The provenance is internal: the construction combines the Library's
actual tensor powers, `tensorPowMulIso`, and
`trivializationOpen_sectionPow`. It is intended for matching an ample
fibre's section cover to a uniform section-lifting threshold. It
contains no assertion that the lifting theorem itself has been proved.
