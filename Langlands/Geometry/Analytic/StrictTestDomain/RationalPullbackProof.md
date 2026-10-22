# Rational inverse images and bounded base change: proof

Author: Worker 247.

The theorem `Langlands.Analytic.StrictTestDomain.rationalPullback` proves
`RationalPullbackStatement.{u,v}`, the target stated and explained in
`RationalPullbackStatement.md`. Fix a complete ultrametric normed field `K`
in universe `u`, presented strict affinoid algebras P and Q, rational data
`d : RationalData K P` and a bounded K-algebra map φ : P → Q. As in the
target, write A for `d.algebra` and α for `d.baseMap : P → A`. Write C for
`(d.pullback φ).algebra` and β for `(d.pullback φ).baseMap : Q → C`. Both are
the existing closed-ideal Tate quotients of the rational equations, over P
and over Q respectively. The pulled-back data have denominator φ(g) and
numerators φ(f_j).

## Direction of the maps

Bounded algebra maps act contravariantly on spectra by seminorm pullback.
Thus φ gives the map M(Q) → M(P), x ↦ x ∘ φ, and α and β give the maps
M(A) → M(P) and M(C) → M(Q). The first clause concerns the inverse image of
the locus of d under M(Q) → M(P). The comparison map i : A → C induces
M(C) → M(A).

## Helpers

All helpers lie in the namespace
`Langlands.Analytic.StrictTestDomain.RationalData`.

- `generatesUnitIdeal`: the denominator and numerators of d generate the unit
  ideal of P. This is the reverse direction of
  `RationalFactorization.generatesUnitIdeal_iff_no_common_zero`, applied to
  `d.no_common_zero`.
- `fraction j` is the actual fraction coordinate
  `RationalLocalization.fractionCoordinate` of A.
  `baseMap_denominator_mul_fraction` gives its equation α(g) · fraction j =
  α(f_j), from `RationalLocalization.coordinate_equation`.
  `comap_baseMap_mem_locus` says that every point of M(A) pulls back into the
  locus, from `RationalLocalization.comap_mem_locus`.
- `hom_ext`: two bounded maps from A to any normed K-algebra that agree after
  composition with α are equal. It applies
  `RationalLocalization.hom_ext_base` with `generatesUnitIdeal`. Within that
  theorem, α(g) is a unit, so the images of the fraction coordinates are
  determined by the base. The target needs no completeness, ultrametric,
  `NormOneClass` or nontriviality hypothesis.
- `hasBoundedMonomials_map_fraction`: for any bounded map a from A to a
  normed K-algebra, the tuple of values a(fraction j) has uniformly bounded
  monomials. The composite of a with the Tate quotient map
  `presentationMap K d.algebra` is a bounded map out of the strict Tate
  algebra. `StrictTateAlgebra.hasBoundedMonomials_map_X` bounds the monomials
  of its coordinate images by the bound of this composite. The fraction
  coordinates are the last d.arity of these coordinates. `pow_bound` extracts
  a power bound for each of them. `hasBoundedMonomials_iff_pow_bound` then
  combines these finitely many power bounds into one monomial bound. This
  includes an empty numerator tuple and a target unit of arbitrary norm.

## Proof

1. **Representation of the inverse image.** `pullback_represents` rewrites
   the inverse image with the published equality `locus_pullback`. It then
   applies `rationalRepresentation` to the data `d.pullback φ` over Q.
   Their absence of common zeros is the field constructed by
   `RationalData.pullback`. This gives closedness of the inverse image,
   equality with the range of M(C) → M(Q), and unique bounded factorization
   for every presented strict affinoid test.
2. **Comparison map.** `hasImageIn_pullback_baseMap_comp` shows that β ∘ φ
   has spectrum image in the locus of d. A point x of M(C) pulls back along β
   into the locus of the pulled-back data, and this membership says exactly
   that x ∘ β ∘ φ lies in the locus of d. The representation property of α
   from `rationalRepresentation`, tested on the presented strict affinoid C,
   therefore yields a bounded map with i ∘ α = β ∘ φ. `comparison` is this
   map, chosen from the unique-existence statement.
   `comparison_comp_baseMap` records its base equation. `comparison_unique`
   proves that any bounded i' with i' ∘ α = β ∘ φ equals it, by `hom_ext`.
   `comparison_fraction` shows that i sends fraction j to the corresponding
   fraction coordinate of C. Applying i to the equation of fraction j shows
   that both elements satisfy the same equation. Its coefficient β(φ(g)) is a
   unit by `RationalLocalization.isUnit_baseMap_denominator` for the
   pulled-back data, so the two elements are equal.
3. **Bounded extension.** Let B be any complete ultrametric normed K-algebra
   in universe `v`. Let a : A → B and b : Q → B be bounded with a ∘ α =
   b ∘ φ. `extension_equation` proves b(φ(g)) · a(fraction j) =
   b(φ(f_j)). The two sides equal a(α(g)) · a(fraction j) and a(α(f_j)) by
   the agreement over P, and these agree by the fraction equation in A. Hence
   the values a(fraction j) are a bounded solution tuple for the equations of
   the pulled-back data over Q. `extension` is
   `RationalLocalization.liftFromBase` applied to b and this tuple. That
   construction evaluates convergent series at the tuple and descends through
   the quotient. `extension_comp_baseMap` (from
   `RationalLocalization.liftFromBase_comp_baseMap`) gives c ∘ β = b.
   `extension_fraction` (from
   `RationalLocalization.liftFromBase_fractionCoordinate`) gives
   c(fraction j of C) = a(fraction j).
4. **Restriction to A.** `extension_comp_comparison` proves c ∘ i = a with
   `hom_ext` over P. Both sides agree after composition with α, since
   c ∘ i ∘ α = c ∘ β ∘ φ = b ∘ φ = a ∘ α.
5. **Uniqueness.** `extension_unique` shows that two bounded maps C → B with
   the same composite with β are equal. This is `hom_ext` for the pulled-back
   data, whose unit-ideal equation is again derived from no common spectrum
   zero. In particular a map satisfying both prescribed restrictions equals
   `extension`, and only its restriction to Q is used.

The closing theorem assembles these results.

The bounded extension is constructed directly in B. It never passes through
the spectrum of B or through tests by presented strict affinoids. B may
therefore be any complete ultrametric normed K-algebra, in a universe
independent of that of K, with no `NormOneClass`, nontriviality, nonzero or
affinoid-presentation assumption. The proof also adds no hypothesis on the
data. Empty numerator tuples, zero and nonreduced quotients, and trivial
scalar valuations remain covered, because no imported result used here
excludes them. The development check of the closing theorem reports only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope relative to the source

The target is a derived formulation based on Berkovich, *Non-archimedean
analytic spaces*, Trieste lectures (2009), Definition 2.1.11 on printed/PDF
page 8, and Definition 2.2.1 and Exercise 2.2.2(ii) on printed/PDF page 9.
The registered original is `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`. The
source fixes the reversed map direction, the rational inequalities and the
no-common-zero condition. The inverse-image clause and the bounded pushout
are derived consequences, not quoted source theorems.

The result is weaker than an all-affinoid domain theorem.

- **Strict tests only.** The representation clause gives unique
  factorization only for test algebras that are presented strict affinoids.
  Berkovich's Definition 2.2.1 tests every morphism from an arbitrary
  k-affinoid space, including non-strict ones. That property is not claimed.
- **Unit radii only.** All rational inequalities have the form
  |f_j(x)| ≤ |g(x)|. The source's rational domains allow arbitrary positive
  radii.

The pushout clause is a universal property among bounded maps into complete
ultrametric normed algebras. The proof does not identify C with a completed
tensor product. It does not compare the Tate quotients with the source's
relative power-series presentations. It constructs no structure sheaf,
analytic space or site.

The shared `RationalData.generatesUnitIdeal` lemma is imported from
[`RationalRepresentationProof`](RationalRepresentationProof.md).
