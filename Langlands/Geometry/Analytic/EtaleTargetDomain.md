# Factoring étale maps through analytic domains

`EtaleTargetDomainStatement` says that an analytic map into a canonical analytic domain is étale if its composite with the domain inclusion is étale. It applies to localized analytic spaces over any complete ultrametric field. The theorem `etaleTargetDomain` proves the proposition, and `etale_of_comp_domainι` gives its morphism-level form.

The proof transports each recognized affinoid piece of the domain to a recognized piece of the ambient space using `DomainEmbeddingRecognition`. Injectivity of the domain inclusion identifies the two inverse-image loci. The two bounded pullbacks differ by the bounded algebra equivalence of the target pieces, so finiteness, pointwise flatness and pointwise unramifiedness descend. The same open source neighborhoods then witness étaleness. For a localized arrow, cancel its source denominator, apply the strong-map argument, and use the étale numerator criterion.

This is derived infrastructure for base change along a domain inclusion, which is a monomorphism. Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), Corollary 3.3.8, printed p. 63 / PDF p. 60, gives preservation of étaleness under base change. The registered source is `berkovich-1993-etale-cohomology`, SHA-256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`. The implemented proof uses the bounded comparison of recognized pieces and the Library's localization.

The localized cancellation theorem `etale_of_comp_domainι` is supplied by [étale domain target cancellation](EtaleDomainTargetCancellation.md).
