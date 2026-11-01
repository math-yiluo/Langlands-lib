# Spectrum embedding for every full affinoid-domain representation

Author: Worker 36.

`Langlands.Analytic.PresentedAffinoidAlgebra.Domain.SpectrumEmbeddingStatement`
states that the actual structural spectrum map of every full affinoid-domain
representation is a closed embedding. This module defines a proposition; it
does not prove injectivity, construct a new represented domain, or assume this
proposition as an axiom.

For every complete ultrametric normed field `K : Type u`, every
`A : PresentedAffinoidAlgebra K`, and every `U : Domain K A`, the conclusion
is `Topology.IsClosedEmbedding U.spectrumMap`. Here `U.algebra` is an actual
finite positive-polyradius quotient presentation, `U.baseMap` is a bounded
unital `K`-algebra homomorphism, and `U.spectrumMap` is its contravariant map
on bounded multiplicative seminorms. The conclusion applies to this stored
map itself.

The imported definition of `Domain` retains a closed subset `U.locus`, exact
equality of that subset with the structural spectrum image, and unique
factorization against every finite positive-polyradius presented-affinoid
test algebra. The quantified domain is unrestricted within that existing
definition. No rational presentation, dense localization, injectivity proof,
strictness, or chart embedding is supplied as an additional hypothesis.
Trivial valuations, arbitrary positive real radii, empty spectra and zero
or nonreduced quotient algebras remain in scope.

`Domain.spectrumToLocus` already continuously corestricts this structural map
to the represented subset, and `Domain.spectrumToLocus_surjective` already
proves its surjectivity. Consequently a proof of the target will supply a
homeomorphism from the actual domain spectrum onto `U.locus` with its subspace
topology, whose forward map is precisely that corestriction. The target uses
a closed embedding to retain the actual structural map without choosing a
homeomorphism in the statement. Since the source spectrum is compact and
the ambient spectrum is Hausdorff, the missing analytic content is
injectivity. The existing uniqueness of bounded restrictions by itself is
not a proof of injectivity on spectrum points.

The original source is V. G. Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1, printed/PDF p. 9, gives the full affinoid-test representation
property used by `Domain`. Fact 2.2.3(i), printed/PDF p. 10, identifies the
representing affinoid spectrum with the represented subset. This target
expresses that identification as a closed embedding, using the existing
exact-image and continuity results. It follows the Library's presentation
category; it neither defines nor proves an equivalence with a separate
category of abstract affinoid Banach algebras.

The rational-chart spectrum embedding already proved in
`GeneralizedAffinoid.RationalChartDomainComposition` is a special case with
an explicit rational quotient and a localization-density argument. It does
not prove this target for arbitrary full represented domains. A proof of
this target, unrestricted domain intersection and composition constructions,
finite rational refinement, structure sheaves, and analytic sites remain
separate obligations.
