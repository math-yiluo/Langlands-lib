# Separation of arbitrary quotient arrows over original-domain covers

This derived construction defines restriction of any arrow in the actual
source-subatlas quotient category along a family of actual original-chart
domain inclusions. It proves injectivity of that restriction map when the
family is a quasinet cover. The field, ambient space, chart index and cover
index have independent universes.

## Provenance and scope

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Definition 1.3.1 on printed p.23 / PDF p.20 fixes the actual domain convention.
Proposition 1.3.2 on printed p.24 / PDF p.21 motivates the morphism separation
assertion, and the G-topology paragraph on printed p.25 / PDF p.22 supplies
the quasinet covering convention. The registered original is
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

This is internal separation for the constructed original-chart model. It
concerns all arrows of its actual source quotient. Existence of glued arrows,
identification with the maximal finite-gluing analytic model, and the full
Proposition 1.3.2 remain separate obligations.

## Implemented construction

`originalDomainInclusion_comp_eq_restrictSubspace` identifies precomposition
by an actual domain inclusion with literal strong source restriction. The
saturated composition formula uses each chart's identical original index.
The intermediate bounded restriction is the identity, so this identifies
whole bounded algebra homomorphisms, not only spectrum-point maps.

`strongFunctor_map_inclusion_comp_ι` cancels the canonical denominator of a
source representative by the proved localization fraction identity.
The nested-selection variant uses the full inclusion diamond.
`exists_commonSourceNumerators` applies quotient induction to two arbitrary
arrows and intersects their refining source selections. It constructs two
full strong numerators on that common source, together with their exact
precomposition equalities in the source quotient.

`domainCoverRestriction` sends an arrow to its precomposites with the actual
domain inclusions. `selectedSourceCover` transports the same domain subsets
to any refining source atlas via the established domain order isomorphism.
Their literal subsets and the quasinet cover condition are unchanged.

To transfer local equality to the common source, the proof composes each
selected-source domain inclusion with the ambient refining inclusion. Its
actual continuous image lies in the corresponding original domain. The
constructed image-only `domainLift` factors this composite through that
domain. Precomposing the given local equality with the factor and rewriting
the exact factorization and common-source identities gives local equality
of the common numerators. The literal domain-restriction comparison turns
this into `StrongLocallyEqualOnDomains`.

The previously proved strong-map separation theorem supplies global quotient
equality of the common numerators. The ambient refining inclusion is a
quasi-isomorphism, so its image under the actual localization functor is
invertible. Cancelling it yields `eq_of_domainCover` for the original
arbitrary quotient arrows. Function extensionality then proves
`domainCoverRestriction_injective`.

No faithfulness of the original strong-map functor, injectivity of bounded
restriction maps, or recovery of algebra homomorphisms from spectrum values
is assumed. Empty covers are allowed precisely when the stated quasinet
cover condition holds.
