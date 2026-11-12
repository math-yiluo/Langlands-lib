# Compact sections and the smooth coreflector

Author: Worker 141.

This is an internal comparison supporting the compact composite proof. For an
arbitrary commutative ring and a topological group acting by continuous maps on
a space with stable neighbourhoods, compact sections of the smooth subsheaf are
naturally isomorphic to smooth vectors in all compact sections. No compactness
of the group or separation assumption on the space is used in this comparison.

The map is induced by the smooth subsheaf inclusion and factored through smooth
vectors. It is injective on sections. A global section fixed by an open subgroup
is locally fixed using the whole space as its neighbourhood, hence belongs to
the smooth subsheaf. The monic inclusion into the original sheaf preserves its
support exactly, so this lift has compact support. This proves surjectivity and
thus gives the natural isomorphism `smoothCompactComparisonIso`.

The result is derived directly from the existing smooth subsheaf and compact
section constructions; it is not the derived composite-functor theorem.
