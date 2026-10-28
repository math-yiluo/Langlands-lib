# Analytic measures for the intermediate-tail parameters

Worker 318's internal construction bundles the existing rectangular product
measure as an `AdditiveHaarMeasure` for every supplied p-adic topological
realization, every supplied additive Haar measure, and all natural row and
column counts. Its measure is definitionally `rectangularMeasure η j t`.
The scalar input and its normalization are retained. No self-duality premise
is needed, so the construction also applies to a supplied self-dual measure.

`scalarHaar_sigmaFinite` installs the published sigma compactness of the
supplied field topology. An additive Haar measure is finite on compact sets,
which gives sigma finiteness on this space. For
`rectangularAdditiveHaarMeasure`, the product is the published iterated
finite product of the same scalar measure. The existing rectangular-product
instance makes it additive Haar. The supplied field topology is
pseudometrizable, sigma compact and second countable. The finite matrix
space inherits these properties; its locally finite Borel measure is regular.
These facts construct the regular additive Haar bundle.

`rectangularMeasure_analytic_properties` records sigma finiteness, regularity,
the additive Haar property, positivity on nonempty open sets, and finiteness
on compact sets for the actual product measure. Positivity and compact
finiteness are inherited from additive Haar. Empty row or column indices
are allowed, including the zero-row product used in the host zeta integrals.

`compatible_quotientMeasure_sigmaFinite` treats every Borel quotient measure
compatible with the specified normalized group and unipotent Haar measures.
The published exact uniqueness theorem identifies this measure with
`unipotentQuotientHaar`, whose sigma finiteness is already proved in
`CanonicalCharacterChange`. The proof transfers that property back to the
caller's measure. It does not select a new normalization or identify measures
whose Haar inputs differ.

The provenance is internal reuse of the named Library constructions and
Mathlib measure and topology instances. These are analytic prerequisites for
the intermediate-tail localization and integral calculation. They provide
neither quotient disintegration nor representation extension nor the closed
intermediate-tail span theorem.
