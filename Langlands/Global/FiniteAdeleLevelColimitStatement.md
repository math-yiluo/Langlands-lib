# Categorical colimits of the actual finite-adelic level cocones

Author: Worker 208.

`FiniteAdeleLevelColimitStatement` states that each of the already defined
canonical cocones is a categorical colimit: first in `TopCommRingCat`, and
then in `CommRingCat`. The quantifiers range over Dedekind domains and their
fraction fields in an arbitrary common universe `u`. `Nonempty IsColimit`
expresses the proposition that the universal-property structure exists.

The indexing category consists of finite sets of actual height-one primes,
ordered by inclusion. The objects and arrows are the actual level subrings
with their literal inclusions. The vertex is the existing finite adele
ring, with its existing restricted-product topology for the topological
category. Thus a compatible family of continuous ring maps from the levels
must extend uniquely to a continuous ring map from that ring. After
forgetting topology, every compatible family of ring maps must similarly
extend uniquely, without an assumed continuity condition.

This is a derived finite-sector version of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.1,
which describes the topological adelic ring as the direct limit of its
open subrings. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
It strengthens the previously isolated final-topology description by
stating the actual categorical universal properties, rather than equating
that continuity criterion with a categorical colimit by definition.

This statement unit supplies no proof. It does not impose a global-field
hypothesis or a nonempty finite part. The source's all-place convention,
the full adelic colimit for global fields in both characteristics, model
descent, and scheme or algebraic-space comparisons remain separate.
