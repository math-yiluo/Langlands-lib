# Ambient isomorphisms of pseudo-parabolic subgroups

Author: Worker 274.

This internal transport module works over every field in universe `u` and
retains all relative scheme tests. It proves that the published
pseudo-parabolic and minimal pseudo-parabolic predicates are invariant under
ambient group-scheme isomorphisms. It does not assert their existence or the
rational conjugacy theorem.

An ambient isomorphism carries a local product factorization to another one
using exactly the original fppf cover. Composing the factors with the
isomorphism preserves their product. Applying the inverse gives the converse.
Consequently `IsFppfProduct.comp_iso` transports both factor functors and the
represented product; it also retains the closed subgroup condition.

`IsUnipotentRadical.comp_iso` and `IsSplitUnipotentRadical.comp_iso` keep the
source group and its structural properties. Normality transports by the
published subgroup-functor preimage operation. For greatestness, a candidate
normal subgroup in the new ambient group is pulled back by the inverse,
compared there, and then mapped forward. This verifies all-test greatestness.

`IsPseudoParabolicSubgroup.comp_iso` transports the ambient smoothness,
connectedness and affineness along the scheme isomorphism. It composes the
cocharacter and radical inclusion with the ambient isomorphism. The published
dynamic functoriality equality identifies the new dynamic parabolic with the
transported one, and the local-product transport proves the required
presentation. The inverse isomorphism proves the stated equivalence.

For minimality, a contained pseudo-parabolic in the new ambient group is
pulled back along the inverse. Minimality in the original group identifies
its all-test image with the original minimal pseudo-parabolic image. Mapping
forward gives the equality required in the new group.
`minimalPseudoParabolicEmbeddingEquiv` packages these mutually inverse maps
as an equivalence on minimal pseudo-parabolic embeddings of any fixed source.
It acts on an embedding by postcomposition with the ambient isomorphism.

The provenance is internal: these constructions and proofs follow from the
published radical, fppf-product and minimality definitions and the existing
dynamic functoriality and range-transport theorems. They require no additional
geometric assertion. For the intended conjugacy application, taking the
ambient isomorphism to be `innerIso g` proves that rational conjugation
preserves both pseudo-parabolicity and minimality. Existence of a rational
point giving containment remains a separate geometric obligation.
