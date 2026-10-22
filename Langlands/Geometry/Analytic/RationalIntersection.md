# Actual intersections of rational localization spectra

Authors: Worker 36 (Lean proof and exposition); Worker 224 (Markdown audit
and submission).

This module proves `RationalIntersection.IntersectionStatement` with the
closing theorem `intersection`, for the closed-ideal Tate quotient
constructed in `RationalIntersection/Definitions`. It identifies the
spectrum of that quotient with the intersection of two finite unit-radius
rational loci in the spectrum of an actual presented strict affinoid
algebra. It also constructs bounded restriction maps from the two original
localization algebras. The only hypotheses are the statement's explicit
unit-ideal conditions `RationalLocalization.GeneratesUnitIdeal`, one for
each original tuple. They concern actual elements of the base algebra.

The original source is Vladimir Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), Exercise 2.2.2(ii)-(iii), printed and PDF p.9.
The retained original is registered as `berkovich-2009-trieste-analytic-spaces`,
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The [author's PDF](https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf)
states the rational quotient formula and closure of rational domains under
intersection. The explicit product presentation and proofs below are the
implemented derivation of the unit-radius algebraic and spectrum part.

## Product tuple and unit ideal

For input denominator/numerator tuples \((g;f_i)\) and \((h;k_j)\),
extend the numerator lists to \(F=(g,f_i)\) and \(H=(h,k_j)\).
The new denominator is \(gh\), and its numerator list contains every
\(F_iH_j\). `numerators` uses the finite-product equivalence
`finProdFinEquiv` to index this list by a single finite ordinal.
`range_numerators` identifies its range with the pointwise product of the
two original generating sets. `generatesUnitIdeal` rewrites the generated
ideal of the product tuple as the product of the two original generated
ideals by `Ideal.span_mul_span`. Its first product is already the new
denominator, so inserting it changes nothing. Since both original ideals
are the whole ring, so is their product. The argument works in the zero
ring as well.

The mixed products \(f_i k_j\) are kept because this argument needs them.
As an informal remark not formalized here: the smaller list of \(f_i h\) and
\(g k_j\) need not generate the unit ideal. For example, in a nonzero algebra
take \(g=h=0\) and \(f=k=(1)\); both original tuples generate the unit ideal,
but \(gh\), \(f_1h\) and \(gk_1\) are all zero.

## Locus equality

`denominator_pos` proves that the denominator has positive value at any
point satisfying the rational inequalities. Otherwise the denominator and,
by the inequalities, every numerator lie in the kernel of the seminorm. Then
the unit ideal lies in that kernel, which contradicts the seminorm taking
value one on one. Positivity is derived, not imposed on the point as
additional data.

For `locus_eq_inter`, the forward direction applies `denominator_pos` to
\(gh\) and the proved unit ideal of the product tuple. This gives positive
values of \(g\) and \(h\). It then cancels them in the inequalities for the
products \(f_i h\) and \(g k_j\). Conversely, multiplying the two original
inequalities, extended by equality at the denominators, proves the
inequality for every product numerator.

## Spectrum

`algebra` and `baseMap` come from `RationalIntersection/Definitions`. They
apply the published rational localization `RationalLocalization.algebra`
and its bounded `RationalLocalization.baseMap` to \(gh\) and the product
tuple. The result is a concrete quotient of a finite Tate algebra by a
closed ideal. The published theorems `RationalLocalization.range_comap_baseMap`
and `RationalLocalization.comap_baseMap_closedEmbedding`, applied with the
proved product unit ideal, give `range_comap_baseMap` (together with
`locus_eq_inter`) and `comap_baseMap_closedEmbedding`. Thus the spectrum
is embedded as a closed subspace whose image is precisely the intersection,
including when that intersection is empty.

## Restriction maps

`coordinate_equation` restates the defining equation
`RationalLocalization.coordinate_equation` of each product coordinate in
pair indices. `isUnit_denominators` derives invertibility of the images of
both original denominators from invertibility of the image of their product,
`RationalLocalization.isUnit_baseMap_denominator`. Cancelling the image of
\(h\), resp. \(g\), proves `left_coordinate_equation`, resp.
`right_coordinate_equation`. They state that the `fractionCoordinate` of
the product \(f_ih\), resp. \(gk_j\), solves the original fraction equation
over \(g\), resp. \(h\), with numerator \(f_i\), resp. \(k_j\).
`fractionTuple_bounded` proves bounded monomials for any finite selection
of these coordinates from the power bounds of the Tate coordinates under the
bounded presentation map of the quotient, rather than inferring bounds from
spectral inequalities. The published constructor `RationalLocalization.liftFromBase`,
which uses convergent Tate evaluation and quotient descent, then defines
`leftMap` and `rightMap`. `leftMap_comp_baseMap` and `rightMap_comp_baseMap`
prove that their compositions with the original base maps equal the
intersection's structural map, by `RationalLocalization.liftFromBase_comp_baseMap`.

## Closing theorem and scope

The closing theorem `intersection` assembles the generated-ideal identity,
locus equality, exact spectrum image, closed embedding, and the two
constructed restriction maps with their base-composition equations in the
statement's order. The target asserts existence of these maps. Their
constructors remain available as `leftMap` and `rightMap`, with the helper
theorems above, for later use.

The proof holds in every universe of the statement. It covers empty
numerator tuples (`m = 0` or `n = 0`), zero and nonreduced quotients, and
trivial valuations on the scalar field. It adds no assumptions beyond the
statement's hypotheses and assumes no spectral-to-power-bound theorem.
This module does not prove that every map with image in the intersection
factors through the constructed quotient, as required by the full
affinoid-domain Definition 2.2.1 of the source. It does not identify absence
of common spectrum zeros with the unit-ideal condition. It does not treat
arbitrary radii, a structure sheaf or an analytic atlas.
