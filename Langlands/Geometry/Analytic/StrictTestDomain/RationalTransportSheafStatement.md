# Sheaf comparison targets for the finite rational transport site

Author: Worker 36, adapting the categorical sheaf criterion from Worker 61's
published `Langlands/Sheaf/Equivariant/Site.lean`.

This module defines proposition-valued proof targets. It proves neither
criterion and asserts no unconditional sheafness or analytic gluing result.
All categories, covering topologies and algebra presheaves in the targets
are the published constructions imported through
`RationalTransportContinuity`.

`SheafCriterionStatement` quantifies over a complete ultrametric normed field
`K : Type u`, a presented strict affinoid algebra `P`, an arbitrary category
`A : Type v` with morphisms in `Type w`, and a presheaf

```
Q : (RationalTransport K P)ᵒᵖ ⥤ A.
```

It asserts that `Q` satisfies Mathlib's `Presheaf.IsSheaf` for the finite
rational transport topology if and only if `inclusion.op ⋙ Q` satisfies that
condition for the ordinary finite rational topology over `P`. These are
sheaf conditions on all covering sieves. Mathlib expresses categorical
sheafness by applying each covariant representable of the value category
and requiring the resulting type-valued presheaf to be a sheaf. No limits,
concrete forgetful functor or completeness assumption on `A` is imposed.
The universes `u`, `v` and `w` are independent.

The ordinary inclusion functor retains the rational presentation and sends
an ordinary inclusion to an arrow labelled by the identity automorphism.
The transport topology covers using finite families of labelled point
images; the ordinary topology covers using finite families of locus
inclusions. The criterion concerns the restriction of a presheaf that
already has maps for all transport arrows. It does not assert that every
ordinary sheaf admits such transport maps, or that the two sheaf categories
are equivalent.

`AlgebraSheafCriterionStatement` quantifies over the same fields and base
algebras and asserts the equivalence of the two sheaf conditions for the
actual commutative `K`-algebra-valued quotient presheaves:
`RationalTransport.algebraPresheaf` and `RationalData.rationalPresheaf`.
The published `inclusionAlgebraPresheafIso` identifies the restriction of
the former with the latter. This statement is a conditional comparison;
it supplies neither sheaf proof. It is separate from the unconditional
analytic gluing and sheaf targets in `RationalSheafStatement`.

`SheafComparisonStatement` is the conjunction of these two targets. They
are named separately so a proof can establish the general criterion and
then derive the actual-algebra specialization using the published
presheaf isomorphism. The specialization uses the generic theorem at the
universes of the commutative algebra category.

The objects remain chosen unit-radius rational presentations over one
fixed base algebra. Distinct presentations with equal loci and distinct
automorphism labels remain distinct. Finite covering index types may be
empty. Empty loci, trivial scalar valuations and degenerate quotients are
allowed. The statement does not claim a result for the full analytic
G-topology, an etale or quasi-etale site, or a continuous topological-group
action.

Provenance is derived. Worker 61's published
`isSheaf_of_isSheaf_inclusion` and `isSheaf_transportTopology_iff` establish
the analogous criterion for transport of ordinary open subsets. The
present targets adapt that criterion to the constructed rational sites;
they are not immediate applications of the open-set theorems because
the categories and covering topologies differ. The expected proof uses
the published continuity for the forward direction and normalization of
transport arrows for the converse: glue the ordinary-inclusion part of
a compatible family and then use translation factorization to verify all
transport arrows. This is a proposed proof route, not a proof in this
statement module. The pinned Mathlib revision is
`5ed2965256430c3649e86755f9576b54eca72435`.

The original geometric context is Berkovich, *Non-archimedean analytic
spaces*, Trieste lectures (2009), printed/PDF p. 9, Definition 2.2.1 and
Exercise 2.2.2(ii)-(iii), and p. 10, the finite-affinoid-cover paragraph
before Fact 2.2.6. These passages support the imported rational-domain and
finite-cover setting, not this categorical comparison. The registered
original is `berkovich-2009-trieste-analytic-spaces`, SHA-256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
