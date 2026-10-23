# Restriction from the finite rational transport site

This module works over a complete ultrametric normed field `K` and a fixed
presented strict affinoid algebra `P`. Objects are the published chosen
unit-radius rational presentations. The ordinary category has locus inclusions
as arrows; the transport category retains a bounded algebra automorphism label
on every arrow. Both sites use their constructed finite covering topologies.
The result constructs restriction from transport-site sheaves to ordinary
rational-site sheaves and compares the actual quotient presheaves.

## Common-label intersection lift

For transport arrows `f : X → inclusion(d)` and `g : X → inclusion(e)` with
`f.label = g.label`, `inclusionInterLift f g h` maps to the published actual
rational intersection `d.inter e`. Its label is `f.label`. Both point-image
conditions show that this common labelled image lies in the intersection.
The definition therefore uses the all-products rational presentation already
constructed in `RationalLimits`, rather than an assumed intersection object.

`inclusionInterLift_left` and `inclusionInterLift_right` prove that composition
with the ordinary intersection projections recovers `f` and `g`. Morphism
equality is proved by equality of the retained labels. An arbitrary pair of
transport arrows is not asserted to be equal.

`label_eq_of_comp_inclusion_eq` gives the equality of labels when
`f ≫ inclusion(a) = g ≫ inclusion(b)`. Ordinary inclusions have label one,
so taking labels of this equation and cancelling these identity factors
gives the required equality. This lemma does not require completeness.

## Continuity and restriction of sheaves

`inclusion_compatiblePreserving` satisfies Mathlib's `CompatiblePreserving`
condition in every universe of type-valued coefficients. Given two transport
arrows with equal composites through ordinary inclusions, the preceding
lemma gives a common label. The intersection lift factors both arrows.
Compatibility of the original family on the ordinary intersection gives
an equality there. Applying the presheaf map along the lift gives the
required equality at the original transport source.

The ordinary inclusion category is thin: its arrows are proofs of locus
inclusion. This is used only for equality of the two ordinary composites
from the intersection. Equality of transport arrows is checked by labels.
The proof uses no additional sheaf hypothesis beyond the interface required
by Mathlib's compatibility-preservation predicate.

`inclusion_isContinuous` combines this result with the published
`inclusion_coverPreserving` using
`CategoryTheory.Functor.isContinuous_of_coverPreserving`.
Consequently, for any coefficient category `A`, `rationalSheafRestriction A`
is a functor

```text
Sheaf (finiteTopology K P) A
  → Sheaf (RationalData.finiteRationalTopology K P) A.
```

Its underlying presheaf is precomposition with `inclusion.op`; its action on
morphisms is the corresponding restriction of natural transformations.
No completeness or limit assumptions are imposed on the coefficient category.
Completeness of `K` is retained for the rational intersection construction
and the finite topologies.

## Comparison of the actual quotient presheaves

`inclusionBoundedPresheafIso` identifies `inclusion.op ⋙ boundedPresheaf`
with `RationalData.rationalBoundedPresheaf K P`. Every component is the
identity bounded map on the same actual quotient algebra. Naturality is
the previously proved `inclusion_restriction`: the transport restriction
along an identity-labelled arrow is the ordinary rational restriction.

`inclusionAlgebraPresheafIso` is obtained by applying the forgetful functor
to commutative `K`-algebras and the functor associator. It identifies
`inclusion.op ⋙ algebraPresheaf` with
`RationalData.rationalPresheaf K P`.

`rationalPresheaf_isSheaf_of_transport` is a conditional consequence:
if the constructed transport algebra presheaf is a sheaf, then the
constructed ordinary rational quotient presheaf is a sheaf. Continuity
first gives sheafness of the restricted presheaf; the comparison
isomorphism transfers it to the ordinary presheaf.

## Provenance and scope

This is internally derived categorical infrastructure. It adapts the
intersection-factorization proof used in the author's published
`RationalContinuity` module, now retaining and comparing transport labels.
It imports the published rational transport category, intersection construction,
finite covering topologies, actual bounded restrictions, and quotient
presheaves. Mathlib supplies the general continuity and sheaf-restriction
constructions in `CategoryTheory/Sites/CoverPreserving.lean` and
`CategoryTheory/Sites/Continuous.lean`.

The original geometric context is Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), printed/PDF p. 9, Definition 2.2.1 and
Exercise 2.2.2(ii)–(iii), and p. 10, the finite-affinoid-cover paragraph
immediately before Fact 2.2.6. The rational-domain, intersection, and finite-cover
context is reused through the existing constructions. The common-label lift,
continuity argument, and presheaf comparisons here are internal deductions,
not claims that this categorical formulation occurs verbatim in that source.
The registered source is `berkovich-2009-trieste-analytic-spaces`, with SHA-256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

This module does not establish the converse implication from ordinary to
transport sheafness, and it does not prove sheafness of either actual
quotient presheaf. Actual finite analytic gluing remains a separate
prerequisite. It also does not construct a full analytic atlas, a general
analytic G-topology, an etale or quasi-etale site, or a continuous
topological-group action. Presentations and automorphism labels remain
distinguished, including on empty loci.
