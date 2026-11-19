# Spectral convergence on represented affinoid domains

`preservedDomainSectionMap` takes the bounded section map of an
automorphism that preserves a represented domain. It takes the identity
outside the locus stabilizer, so a family of these maps can be tested
along a filter on its ambient parameter type.

Suppose bounded automorphisms of a presented affinoid algebra converge
spectrally to the identity on every element. For a weighted rational
chart, compactness gives a positive lower bound for the denominator on
its locus. A sufficiently small denominator displacement leaves its
value unchanged there. Bounds for the finitely many numerator
displacements preserve their defining inequalities. Pullback of a
spectral bound through the inverse automorphism gives the same
displacement bound for that inverse. Both maps therefore preserve the
locus on the same filter event.

The restricted bounded maps commute with the rational structural map,
so their displacement converges on the base sections. For a unit, the
difference between the images of its inverse is the difference between
the images of the unit multiplied by the two images of the inverse,
with a minus sign. The two outside factors admit uniform spectral
bounds from the norm of the original inverse. This controls the new
fraction coordinates. Approximation by polynomials in the weighted
coordinates gives convergence on the entire rational quotient.

`DomainAutomorphism.eventually_spectralBound_sectionMap` takes a finite
ambient rational cover of an arbitrary represented domain. The finite
family of rational preservation events gives preservation of the whole
domain. Its bounded restriction maps commute with the section maps,
and the component spectra jointly detect the spectral bound on each
section of the domain. The parameter is an arbitrary filter. The
lemmas derive this restriction property from the Library's
`SpectralConvergesOn`, rational presentations and full domain
representation, for use in continuity tests on analytic pullbacks.
