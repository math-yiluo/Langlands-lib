# Rational comparison over a target quotient

Author: Worker 135.

This module constructs the bounded comparison needed to move a finite rational
cover of a rational target to a cover of the entire spectrum of its actual
quotient algebra. It transports compatible section tuples and proves the
empty-cover case. It does not prove general finite-cover analytic descent.

All constructions use the existing `RationalData` and actual closed-ideal Tate
quotients. The scalar field K is complete and ultrametric; all presented
algebras, rational data and index types have the same universe u. No nonzero,
reducedness or nontrivial-valuation hypothesis is imposed. The transport lemmas
do not need finiteness of the covering family.

## The relative comparison

Let `h : e → d` be an inclusion of rational loci over a presented strict
affinoid P. The original restriction is a bounded map
`h.restriction : d.algebra → e.algebra`. Pulling e back along `d.baseMap`
gives rational data over `d.algebra`, with the existing comparison
`e.comparison d.baseMap : e.algebra → (e.pullback d.baseMap).algebra`.

`Inclusion.relativeInverse` constructs its inverse using the published
`RationalData.extension`, with the identity map on `e.algebra` and the
restriction from `d.algebra`. These maps agree on P because restrictions
commute with the actual base maps. The extension equations show that the
inverse composed with the new base map is the old restriction, and that
inverse followed after comparison is the identity on `e.algebra`.

`comparison_comp_restriction` identifies comparison after the old restriction
with the new base map. Its proof compares both bounded maps after the base
map from P, then uses the existing `d.hom_ext`. Applying the analogous
extensionality result to the pulled-back domain proves the second inverse
identity. `relativeEquiv` packages these two constructed bounded maps and
identities into a `BoundedAlgEquiv`; `comparison_injective` records its
injectivity. In particular the equivalence is proved from the locus inclusion,
not supplied as a hypothesis.

## Coverings and pairwise restrictions

`FamilyCovers.relative` sends every spectrum point of `d.algebra` to its
image in d's locus, then applies the given covering condition. Consequently
the pulled-back D(i) cover the entire spectrum of `d.algebra`.

`intersectionComparison` first uses the existing comparison for `d.inter e`,
then restricts along the inverse arrow of `pullbackInterIso`. Its target is
the algebra of the intersection of the pulled-back inputs. This explicitly
handles the distinction between the chosen presentation of a pulled-back
intersection and the chosen intersection of pulled-back presentations.

The base-map equation for this comparison follows from the existing
comparison and restriction equations. Extensionality on the original base
then proves its commutation with each of the two intersection restrictions.
`compatible_comparison` applies the intersection comparison to the original
compatibility equality and uses these two commuting squares. Thus the tuple
`(D i).comparison φ (s i)` is compatible for the pulled-back intersections
for any bounded base-change map φ.

## Empty coverings

`subsingleton_algebra_of_locus_empty` uses the published nonemptiness theorem
for the spectrum of every nonzero presented strict affinoid. If the quotient
were nontrivial, that theorem would supply a point of its spectrum, whose
image under the base map belongs to the empty locus, a contradiction. This
argument uses the actual spectrum nonemptiness theorem, including its
trivially valued case; no pointwise vanishing criterion for individual
functions is used.

For an empty index type, the covering condition implies that the target
locus is empty. `subsingleton_algebra_of_empty_cover` therefore gives a
subsingleton quotient algebra. `existsUnique_gluing_empty` chooses its zero
element; all restriction conditions are vacuous and uniqueness follows from
subsingletonness. Neither nonemptiness of the cover nor compatibility needs
to be assumed in this case.

## Provenance and scope

These are derived constructions and elementary consequences of the published
rational universal properties, base change, intersection and spectrum
nonemptiness results. They are not standalone assertions quoted from a
source. The geometric context is Berkovich, *Non-archimedean analytic spaces*,
Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`:
Definition 2.2.1 and Exercise 2.2.2(ii)–(iii), printed/PDF p. 9, describe
affinoid domains, rational quotients and intersections. Fact 2.2.6(i), p. 10,
states the stronger finite-cover Tate acyclicity result that motivates the
remaining analytic descent obligation.

The implemented comparisons use unit radii and the existing universal
properties tested on presented strict affinoids. This module does not prove
Tate acyclicity, general finite gluing, categorical sheafness, higher Cech
exactness, admissibility, arbitrary-radius comparisons or an analytic atlas.
The nonempty finite-cover descent step is still needed to prove
`FiniteRationalGluingStatement`.
