# Actual source Jacquet comparison

This internal comparison identifies the actual normalized source Jacquet
functor with the literal standard Jacquet restriction, after the required
subgroup identities have been supplied. It proves neither a structural
identity nor rational induction compatibility.

`conjugationFunctorOneNatIso` makes the published
`conjugationFunctorOneIso` natural. Its components are the existing identity
linear isomorphisms; naturality follows because pullback keeps each
intertwining linear map. `identityConjugationMembership` turns an equality of
ambient subgroups into the membership witness for conjugation by the identity.

`leviNormalizedJacquetIsoOfEq` works for arbitrary closed subgroups of a locally
compact nonarchimedean group, with independent group and representation-carrier
universes. It assumes two actual semidirect decompositions inside the same
closed group `M`, equality of their ambient Levis, and equality of their
radicals after restriction to `M`. It eliminates the Levi equality. The
normalized Jacquet functor depends on the restricted radical, the restricted
Levi and its normalizer relation; it does not depend on the parabolic or on its
projection. Equality of restricted radicals therefore identifies these
functors, using proof irrelevance for their closedness and normalizer witnesses.
Both are transported from the restricted Levi to the same ambient Levi by the
published `subgroupOfContinuousEquiv`. The identity-conjugation natural
isomorphism removes the final identity transport.

`geometricSourceJacquetComparisonIso` applies this law to the actual
`GeometricK0Target` source intersection. For arbitrary finite labels `I,J,K`
and arbitrary `n`, it assumes the actual source decomposition, a standard
restricted decomposition at `K`, the inclusion `M K ≤ M J`, and the exact
identities

`M J ∩ n⁻¹ (M I) n = M K`,

`(M J ∩ n⁻¹ (U I) n).subgroupOf (M J) = (U K).subgroupOf (M J)`.

The resulting natural isomorphism compares the full actual normalized smooth
functors. Its left side is `geometricSourceJacquetFunctor` followed by the
identity identification of its actual intersection Levi with `M K`; its right
side is `leviNormalizedJacquetFunctor` of the literal restricted family.
Closedness of the actual source radical is derived by intersection and
conjugation, exactly as in the geometric source functor.

The source parabolic identity is needed to derive the actual source
decomposition from standard structural data. Once both decompositions are
supplied, only the Levi and radical identities are needed for this Jacquet
comparison. No source-parabolic identity, finite-length preservation, stages
identity, Weyl conjugacy, geometric expansion or Coxeter realization is inferred.
The provenance is the published definitions of `normalizedJacquetFunctor`,
`leviNormalizedJacquetFunctor` and `geometricSourceJacquetFunctor`, together with
the published identity-conjugation object isomorphism. There is no additional
literature assertion or classification argument in this comparison.
