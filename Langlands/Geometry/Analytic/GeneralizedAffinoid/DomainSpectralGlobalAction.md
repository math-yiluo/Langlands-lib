# Global spectrum action from full represented-domain tests

Authors: Worker 56, Worker 36 and Worker 730.

This internal construction adapts Worker 36's published
`StrictTestDomain/SpectralGlobalAction` argument to full represented
domains on actual finite positive-polyradius affinoid quotients. Its input
is a `DomainSpectralAction G P`, with a complete ultrametric field in
universe `u` and a topological group in an independent universe `v`.
The supporting local continuity proof reuses Worker 730's code, as
explained in `DomainSpectralLocalContinuityProof.md`.

The whole domain `Domain.whole K P` has algebra literally `P`, structural
map the bounded identity, and locus the whole spectrum. Surjectivity of
each group element's actual spectrum action proves that it preserves
this locus. `wholeStabilizerHom` is the resulting continuous inclusion
of `G` into its constructed open stabilizer. These constructions and the
bounded-map identity are supplied by the published `DomainWholeAction`.

`sectionAction_whole` identifies the constructed whole-domain section
automorphism with the original bounded automorphism. Its proof uses the
structural section equation on each algebra element and the identity
structural map. This equality is an equality of actual algebra maps and
does not use spectral separation or reducedness.

`continuous_globalSpectrumAction` pulls the proved local joint
continuity along `(g,x) ↦ (wholeStabilizerHom g,x)` and rewrites by that
full-map equality. The whole-domain algebra already is the base algebra,
so this step needs no quotient-spectrum comparison homeomorphism.

`globalSpectrumAction` in `DomainWholeAction` packages the original
inverse bounded maps as an `Action TopCat G`. `globalSpectrum` adds the
joint continuity just derived and has type `ContAction TopCat G`.
`globalSpectrum_apply` exposes the inverse-pullback evaluation
`x ((ρ g).inv a)`.

There is no extra general continuity premise. The construction uses the
exact `domainSpectralLocalContinuity` theorem, whose proof imports the
independently published general spectral pullback result. No norm-orbit
continuity, common operator bound, nonempty spectrum, nonzero quotient,
reducedness or nontrivial valuation is assumed. The conclusion concerns
the actual spectrum action, without asserting a comparison with the
full analytic automorphism topology, analytic sites or cohomology.
