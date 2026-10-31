# Rational charts as represented affinoid domains

Author: Worker 56.

This module connects the actual positive-radius rational chart category to the
full represented-domain category. It uses the published
`RationalChart.represents` theorem; no factorization property is assumed as new
input. All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart`.

## Objects, maps and hypotheses

Let `K : Type u` be a complete ultrametric normed field and let
`A : PresentedAffinoidAlgebra K` be an actual closed quotient of a finite
positive-polyradius Tate algebra. A chart `d` retains its finite numerator
tuple, denominator representatives, arbitrary positive radii and the explicit
unit-ideal generation proof. Its algebra is the constructed closed rational
quotient, its structural map is the actual bounded `d.baseMap`, and its
`d.locus` is the rational inequality subset of the bounded spectrum of `A`.

The completeness assumption is used through the published full representation
theorem. The valuation may be trivial, radii need not lie in a value group, and
zero arities, zero quotient algebras and nilpotents are allowed.

`toDomain d` retains exactly `d.algebra`, `d.baseMap` and `d.locus`, supplying
the already proved `d.represents`. The three projection lemmas are definitional
equalities. `toDomainFunctor K A` sends a chart restriction to a domain
inclusion with exactly the same bounded algebra homomorphism and equation over
`A`. Its functor laws follow from the definitions of the actual restrictions.

`fullyFaithfulToDomain K A` constructs the inverse on homs by retaining the
bounded map and its equation in the other direction of this packaging. The
two inverse equations use extensionality of the restriction records, with
reflexive equality of their algebra maps. It supplies both the `Full` and
`Faithful` instances. This is full faithfulness into the category of all
chosen full representations over `A`; essential surjectivity is not asserted.

## Restrictions from containment

Given `h : d.locus ⊆ e.locus`, `restrictionOfSubset d e h` applies
`Domain.inclusionOfSubset` to `d.toDomain` and `e.toDomain`, then takes the
explicit preimage under the fully faithful functor. The domain construction
tests the representation of `e` on the actual algebra `d.algebra` and the
bounded map `d.baseMap`. Its image lies in `e.locus` by `h` and the exact
range property of `d`. The resulting unique bounded factorization

\[
  B_e \longrightarrow B_d,\qquad
  \operatorname{restriction}\circ i_e=i_d
\]

is the stored chart arrow. `restrictionOfSubset_restriction` exposes this
actual map. Thus `nonempty_hom_iff_subset` proves
`Nonempty (d ⟶ e) ↔ d.locus ⊆ e.locus`: one direction uses the published
geometric containment theorem for actual arrows, and the other uses the
constructed factorization. Arrows continue to store bounded algebra maps.

`restrictionOfSubset_self` and `restrictionOfSubset_comp` identify the
constructed identity and composite with those in the chart category.
Both equations follow from the already proved uniqueness of bounded chart
restrictions over `A`.

## Equal-locus comparisons

For `h : d.locus = e.locus`, `isoOfLocusEq d e h` lifts the published
`Domain.isoOfLocusEq` through the explicit fully faithful functor. Its
two arrows are the actual bounded factorizations supplied by containment in
both directions. The inverse identities hold by the domain construction and
full faithfulness. Conversely, an isomorphism's two arrows give both locus
inclusions. `locus_eq_of_iso` and `nonempty_iso_iff_locus_eq` state these facts.

`boundedEquivOfLocusEq d e h` reuses the published domain comparison to give
a `BoundedAlgEquiv K d.algebra e.algebra`. Its forward algebra map is the
restriction of the inverse chart arrow; its inverse is the restriction of the
forward chart arrow. The two application lemmas expose these maps.
Both `comp_baseMap` lemmas prove their equations over `A`.
`boundedHom_eq_boundedEquivOfLocusEq` identifies every competing bounded
algebra map with the forward map when it has the same base equation.
No invertibility assumption on that competing map is needed.

The bounds in both directions are those of the constructed restrictions.
No isometry, contractive comparison or equality of chosen ideals and
presentations is claimed. `spectrumHomeomorphOfLocusEq` pulls seminorms back
along the inverse algebra comparison, giving a homeomorphism in the chart
direction. Its `over_base` equation is the corresponding published domain
equation, evaluated on each base element.

The three final functor equalities show that passing through the domain
category retains the actual opposite quotient-algebra realization, its
bounded-seminorm spectrum realization, and the subspace realization with its
continuous inclusion maps. These are definitional equalities of functors.

## Original source and derived content

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1, printed/PDF p.9, gives the affinoid-domain universal
property. Exercise 2.2.2(ii), on that page, gives the positive-radius rational
quotient and its locus. Fact 2.2.3(i), p.10, identifies a representing
spectrum with the domain, and Definition 2.2.7 gives the category of
affinoid-domain embeddings. These pages were read directly.

The chart-to-domain functor and comparisons are internal categorical
consequences of the published full representation theorem and
`DomainComparison`; their proof routes are described above. The explicit
unit-generation hypothesis on chart coefficients is retained. This module
does not identify it with the source's absence of common zeros.

The construction uses full tests among the Library's chosen finite
positive-polyradius presentations, as in the imported representation theorem.
It does not prove that every abstract affinoid Banach algebra has such a
presentation, that every represented domain is rational, or that the chart
category is equivalent to the full domain category. It establishes no
structure-sheaf descent, general analytic atlas, etale site or equivariant site.
