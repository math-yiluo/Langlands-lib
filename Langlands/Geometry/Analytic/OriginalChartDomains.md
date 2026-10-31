# The order and actual presentations of original-chart domains

This module bundles the subsets of a supplied genuine affinoid atlas that
satisfy its concrete contained-original-chart quasinet condition. It constructs
their intersection order and realizes its inclusions by actual chosen bounded
atlas maps. Coefficients, ambient points and chart indices retain the independent
universes `u`, `v` and `w`. The coefficient field is complete and ultrametric;
the affinoid algebras are not required to be reduced.

`isOriginalChartDomain_univ` derives the whole-space condition directly from
the ambient quasinet. The finite witness at each point has all members
contained in the whole space, and its ambient neighborhood is the required
relative neighborhood. `IsOriginalChartDomain.inter` applies the published
intersection theorem, which constructs finite witnesses and refines member
intersections using the ambient net.

`OriginalChartDomain` contains only an actual subset and a proof of that
topological condition. Its `SemilatticeInf` order is subset inclusion, and
its infimum is literal set intersection. Its `BoundedOrder` has the whole
space as top and the empty subset as bottom. `ofChart` bundles any original
spectrum range using its proved domain condition.

`originalDomainPresentation` applies the constructed subspace-atlas
constructor to each bundled domain. Its space has the induced topology;
its chart indices are exactly the original charts whose entire range is
contained in that subset. It retains their genuine affinoid algebras and
bounded restrictions. `originalDomainMap` realizes subset inclusion by the
actual continuous subtype inclusion, the same original chart indices and
bounded identity algebra maps. The complete-arrow identity and composition
laws give `originalDomainFunctor`. The actual ambient inclusions form
`originalDomainCocone`, and the two intersection inclusions agree after
inclusion into the ambient atlas.

`originalDomainPresentation_ofChart` recovers the previously constructed
original-chart presentation exactly. `originalDomainTopInverse` sends a
point to the whole-space subtype and an original index to the same index
with its whole-space containment proof. Its bounded pullbacks are identities.
Together with the whole-space inclusion, it gives `originalDomainTopIso`.
Both inverse laws are equalities of the entire chosen arrows, including
their dependent bounded pullbacks.

These constructions are internal derived infrastructure from Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993), registered as
`berkovich-1993-etale-cohomology`: section 1.1, printed pp.13–14 / PDF
pp.10–11 (contained-member families, induced subspaces and quasinets), and
Definition 1.2.3 and Remark 1.2.4(i), printed p.16 / PDF p.13 (actual affinoid
atlases and bounded restrictions). The order, functor and isomorphism are
derived consequences, not separately attributed source theorems.

The domain condition uses only charts already in the fixed atlas. It does
not assert that every open subset or every analytic domain satisfies that
condition. No new affinoid domains, saturated atlas, unrestricted gluing,
covering topology or analytic site are constructed here.
