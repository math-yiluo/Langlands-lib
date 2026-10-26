# Bounded transport through the relative-series comparison

Author: Worker 56.

This module derives bounded transport for unconstrained finite variable adjunction from the published `RelativeSeriesComparison` and coefficient-map constructions. Work over a complete ultrametric normed field K. Let A and B be actual presented affinoid algebras, let m be the number of new variables, and let s be their positive real polyradius. The base presentations may have different arities, radii and closed ideals.

`relativeSeriesEquiv K A s` packages the published `relativeSeriesMap` and `relativeSeriesInverse`, with their proved inverse identities, as a `BoundedAlgEquiv` between `Adjoin.algebra K A s ∅` and `GeneralizedTateAlgebra s A`. Both directions preserve the imported quotient and weighted coefficient norms exactly. The inverse norm equality follows by applying the forward norm equality to a reverse image and using the forward-reverse identity.

For any actual bounded K-algebra map φ from A to B, `relativeSeriesTransport K s φ` is the composition of the forward comparison for A, the existing `mapCoefficientsAlgHom s φ`, and the reverse comparison for B. Thus its relative-series expression applies φ to every coefficient. It sends `baseMap a` to `baseMap (φ a)` and fixes the labels of the new coordinates. The coefficient-map identity and composition laws, together with the comparison inverse identities, prove the corresponding laws on the actual enlarged quotients.

Every supplied nonnegative constant c bounding φ also bounds the transported map with exactly the same c. This uses norm equality for both comparison directions and the published coefficient-map bound. If φ preserves norms, its coefficient map preserves the weighted norm and its transport preserves the quotient norm, hence is an isometry.

`relativeSeriesTransportEquiv K s e` transports any supplied bounded base equivalence e. Its forward map is the transport of e and its inverse is the transport of `e.symm`. The transport composition and identity laws prove the two inverse identities. Every supplied nonnegative forward or inverse bound transfers unchanged. The construction requires bounds in both directions as present in `BoundedAlgEquiv`; it makes no use of an open mapping theorem.

This is an internal derived construction, rather than a numbered assertion from the literature. Its analytic series conventions come from Berkovich, *Non-Archimedean analytic spaces*, Trieste lectures (2009), Definition 2.1.6(i), printed/PDF page 8, as documented in the imported comparison statement. The comparison and coefficient maps are reused by their published Lean names; this module introduces neither a coefficient-lifting hypothesis nor an assumed comparison.

The hypotheses retain arbitrary positive real new radii, trivial valuations, empty variable blocks, nonproper ideals and zero quotients. Transport uses a given bounded map or equivalence of the actual base algebras. The module does not construct such an equivalence between arbitrary presentations, compare further equation quotients, or construct analytic domains, sheaves or etale sites.
