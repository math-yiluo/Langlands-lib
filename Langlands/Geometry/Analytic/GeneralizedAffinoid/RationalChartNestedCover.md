# Finite full-domain covers through nested actual rational charts

Author: Worker 56.

This module constructs an equivalence between the categories of finite
full-domain covers of an inner domain and of its transport through an actual
rational-chart inclusion. Cover morphisms retain their chosen component
indices and actual bounded restrictions. The inverse accepts every cover of
the transported domain. The module also proves the actual component-spectrum
and total-spectrum comparison equations and preserves composition of covers.

The field `K` is complete and ultrametric. The ambient algebra `A` is an actual
chosen finite positive-polyradius Tate quotient by a closed ideal. The charts
`d` and `e` are rational charts over `A`, with explicit unit generation.
An arrow `f : d ⟶ e` stores a bounded map
`f.restriction : e.algebra → d.algebra` and its equation over `A`.
Its spectrum map is the actual inclusion in the space direction.
The input `U : Domain K d.algebra` is a full represented domain, including
its representing algebra, bounded structural map and universal property
against all presented affinoid tests.

The preceding `RationalChartDomainNaturality` construction transports it to
`nestedDomain f U : Domain K e.algebra`, retaining `U.algebra` and setting
its structural map to `U.baseMap.comp f.restriction`. Its locus is exactly
`f.spectrumMap '' U.locus`. Write `H_U` for the constructed
`nestedDomainLocusHomeomorph f U`, whose forward map is `f.spectrumMap`.
These domains and homeomorphisms are the actual constructions used below.

## Coverage and the forward functor

`familyCovers_nestedDomain_iff` preserves and reflects pointwise coverage
for any indexed family of domains over `d.algebra`; the index type may have
an independent universe. It uses the exact image-locus equation. To reflect
coverage, apply the transported coverage at `f.spectrumMap x`, then use
the proved injectivity of this spectrum map to recover membership of `x`
in the chosen original component. To preserve coverage, choose an original
preimage of a transported point and cover that preimage. No component
inclusion maps are required for this family-level statement.

A `Domain.FiniteCover U` stores a size, domains indexed by `Fin size`,
actual inclusions into `U`, and pointwise coverage. `nestedFiniteCover f c`
keeps its size and transports each component and inclusion by
`nestedDomainFunctor f`. The coverage theorem supplies the new covering
proof. The projection lemmas expose the same size, the transported component,
the unchanged component algebra and the unchanged bounded map of its
inclusion into the target. The singleton identity cover is preserved
definitionally.

For a chosen-index refinement `r : Refinement b c`,
`nestedCoverRefinement f r` retains `r.index` and transports `r.map i`
by the domain functor. Its projection lemmas identify both the bounded
component restrictions and the map of the disjoint union of component
spectra with their originals. `nestedFiniteCoverFunctor f U` packages
these operations as a functor on the actual refinement categories.
The functor laws follow from `Refinement.ext`, since the chosen index
functions agree and each relevant domain hom-set is a subsingleton.
The canonical refinement to the singleton cover is preserved as well.

`fullyFaithfulNestedFiniteCover f U` constructs a preimage of every
refinement between transported covers: keep its index function and use
`fullyFaithfulNestedDomain f` to recover each original component inclusion.
This retains each supplied bounded restriction. The two preimage projection
lemmas expose these choices, and refinement extensionality gives the hom
inverse laws. The construction supplies both `Full` and `Faithful`
instances.

## An inverse on arbitrary transported covers

Let `c` be any finite cover of `nestedDomain f U`. Its components need not
be supplied as transports of inner domains.
`nestedAmbientFiniteCover f c` first extends each actual component
through `e`. It extends its target inclusion through `e` and composes with
`(extendNestedDomainIso f U).hom`, restoring the target to
`d.extendDomain U`. The existing ambient extension of `c` covers its
original target; equality of target loci under this actual domain
isomorphism proves coverage of the restored target.
`nestedAmbientFiniteCoverFunctor f U` applies this construction to
refinements with their indices and extended component maps retained.

`nestedFiniteCoverInverse f U` then composes that functor with
`d.restrictExtendedFiniteCoverFunctor U`. The latter performs actual
localization through `d` and restores the inner target to `U`.
This constructs a full represented component domain over `d.algebra`
for every supplied outer component, using the existing representation
proofs for domain extension and rational-chart localization.

The inverse projection lemmas identify its size and component algebras
with those of `c`. For every component `i`, its bounded structural map is
exactly

```text
(c.map i).restriction.comp U.baseMap.
```

Its inclusion into `U` has bounded restriction `(c.map i).restriction`.
For every refinement the inverse retains its chosen index function,
bounded component restrictions and disjoint-union spectrum map.
Thus the inverse is defined on the whole target cover category.

`nestedAmbientExtendCoverIso f c` compares ambient restoration after
forward cover transport with direct extension of `c` through `d`.
It uses the identity index function and the actual
`extendNestedDomainIso` on every component, in both directions.
Naturality follows from refinement extensionality, giving
`nestedAmbientExtensionNatIso f U`.

## Unit, counit and equivalence

`nestedFiniteCoverUnitIso f c` compares an inner cover with its
inverse-after-forward round trip. `nestedFiniteCoverCounitIso f c`
compares the forward-after-inverse round trip with every outer cover.
Each direction has identity indices and the actual identity bounded map
on every retained component algebra. The necessary structural equations
are the original component inclusion's `comp_baseMap` equation, in the
appropriate direction. All eight index and bounded-map projection lemmas
expose these maps.

Refinement extensionality proves both inverse laws, naturality of the unit
and counit, and the triangle identity. `nestedFiniteCoverEquivalence f U`
therefore constructs

```text
Domain.FiniteCover U ≌ Domain.FiniteCover (nestedDomain f U)
```

with the forward and inverse functors described above. The output
equivalence and its arbitrary-cover inverse are constructed from the given
domains and actual bounded restrictions.

## Actual spectrum diagrams and composed covers

For a cover `c`, `componentMap i` maps the actual Banach spectrum of
`(c.obj i).algebra` into the target locus. `totalMap` assembles these maps
on their topological disjoint union. The component algebras are unchanged
by both cover functors, so these spectrum sources are literally the same.
`nestedFiniteCover_componentMap` and `nestedFiniteCover_totalMap` prove

```text
(nestedFiniteCover f c).componentMap i = H_U.comp (c.componentMap i)
(nestedFiniteCover f c).totalMap       = H_U.comp c.totalMap.
```

The component proof uses continuous-map and subtype extensionality, then
equality of seminorm values on every element of `e.algebra`. The total
equation evaluates the component equation at each disjoint-union point.

The inverse component and total equations say that applying `H_U` to
the inverse cover's maps recovers the original outer cover's maps.
The inverse component proof evaluates the outer inclusion's actual
`comp_baseMap` equation under a component spectrum point. It thereby
compares the two bounded-map composites on every algebra element.
The total equation again follows componentwise.

`nestedCoverRefinement_spectrumMap_over_target` and
`nestedFiniteCoverInverse_spectrumMap_over_target` combine these total
equations with the original refinement's commuting spectrum triangle.
They give commuting diagrams over the actual target locus homeomorphism
for both functors, using the retained refinement spectrum maps.

Finally, `nestedFiniteCover_bind` proves that transporting a cover
composed with finite covers of its components equals composing all the
transported covers. This equality is definitional: the construction keeps
the sizes, the same `Fintype.equivFin` enumeration of the finite sigma
type, and every actual bounded composite in `FiniteCover.bind`.

## Source and construction scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF p.9, Definition 2.2.1, gives the full affinoid-domain
universal property, and Exercise 2.2.2(ii) gives arbitrary positive-radius
rational quotients. Printed/PDF p.10, Fact 2.2.3(i), gives the
representing-spectrum identification context, and Definition 2.2.7 gives
actual affinoid-domain embeddings. The finite affinoid covering convention
also appears on p.10 immediately before Fact 2.2.6.
These original pages were read directly.

The cover functors, arbitrary-cover inverse, equivalence and spectrum
diagrams are internal consequences of the preceding actual nested-domain
and cover-localization constructions. The implemented derivations are
described above; they are not separately numbered assertions of the
original. Chosen positive-polyradius presentations and explicit unit
generation remain in force. The latter is not identified here with the
source's absence-of-common-zeros condition.

The transported components are full represented domains. No single rational
presentation over the outer chart is constructed, so this module does not
establish the rational-flattening assertion of Exercise 2.2.4. It does not
assert the algebra/module acyclicity or descent of Fact 2.2.6, arbitrary
domain base change, a presentation theorem for all abstract affinoids,
analytic atlases, or etale/equivariant sites. Empty covers when the target
locus is empty, empty loci, zero algebras, nilpotents, trivial valuations
and arbitrary positive radii remain permitted.
