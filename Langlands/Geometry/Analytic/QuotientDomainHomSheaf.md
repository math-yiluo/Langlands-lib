# The actual quotient-Hom sheaf on original-chart domains

Author: Worker 36.

This internal construction proves that the previously constructed actual
quotient-Hom domain presheaf is a sheaf for the original-chart quasinet topology.
It uses the proved arbitrary quotient relative-domain gluing construction and
all-covering-sieve separatedness. The bundled sheaf and its morphisms use
Mathlib's existing definitions of sheaves of types. No new original-literature
assertion is introduced.

For a covering sieve `R` over an arbitrary original-chart domain `S`,
`exists_domainSieveAmalgamation` indexes every member by its source domain, its
actual arrow to `S`, and the proof that this arrow belongs to `R`. Each local
map is exactly the given compatible family's element for that arrow. On the
intersection of two source domains, the two inclusion arrows have equal
composites to `S`, since the original-domain category is an inclusion order.
The family's ordinary presheaf compatibility therefore proves the complete
quotient overlap equation. This constructs a `QuotientDomainMatchingFamily`
without choosing global strong representatives for its arbitrary quotient
arrows.

The covering-sieve hypothesis supplies finite relative neighborhood witnesses
for its source subsets. Each such source is among the indexed domains, so
monotonicity of local refinement gives the relative quasinet cover needed by
`glueRelative`. Apply that actual relative gluing construction. Its recovery
formula at the index consisting of an arbitrary sieve member is precisely the
ordinary presheaf amalgamation equation for that member. This proves
amalgamation on the entire sieve, including sieves over proper or empty domains;
the argument does not reduce the hypothesis to pointwise set coverage.

`domainHomPresheaf_isSheaf` combines this existence with the proved separatedness
for every covering sieve using Mathlib's `Presieve.IsSeparated.isSheaf`. The
result is the usual sheaf condition for every sieve of the original-domain
quasinet topology. `domainHomSheaf` bundles the unchanged actual quotient-Hom
presheaf as a Mathlib `Sheaf` through the existing equivalence between the
presheaf and type-valued sheaf conditions. Its sections on `S` are the actual
quotient arrows from the constructed presentation `A.originalDomain S` to the
fixed target. Its restriction maps are precomposition with the constructed
actual domain arrows, as in `domainHomPresheaf`.

`domainHomSheafMap` bundles the already proved natural postcomposition map for
any actual quotient arrow between targets as a morphism of these sheaves. No
change to its component functions or naturality equation is required.

The field, ambient-space and chart-index universes are independent. All indexing
objects in the sieve construction have the sizes of the existing domain and
arrow categories; the relative gluing result it uses permits independent
cover-index universes. The field is complete and ultrametric, with trivial
valuations and empty domains allowed. The result concerns the actual quotient
morphisms on the constructed fixed-original-chart domain site. Identification
with the full analytic category, construction of the etale and equivariant
sites, and the Harris specialization remain subsequent obligations.
