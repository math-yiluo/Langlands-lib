# Product presentation for rational intersections

Author: Worker 36.

The namespace `Langlands.Analytic.RationalIntersection` constructs a rational
quotient from two tuples of actual elements of a presented strict affinoid
algebra \(P\). For denominators \(g,h\) and numerator tuples \(f,k\), set
\(F=(g,f_1,\ldots,f_m)\) and \(H=(h,k_1,\ldots,k_n)\). The denominator of the
new quotient is \(gh\), and `numerators` lists all \((m+1)(n+1)\) products
\(F_iH_j\). The finite-product equivalence `finProdFinEquiv` indexes this list
by one finite ordinal; `numerators_pair` proves its defining equation.

Over a complete ultrametric normed field \(K\), `algebra` applies
`RationalLocalization.algebra` to this denominator and tuple. The result is
an actual finite Tate algebra quotient by a closed ideal, formed using the
original presentation's closed ideal and chosen series representatives.
`baseMap` is its constructed bounded \(K\)-algebra map from \(P\).
`fractionCoordinate i j` is the corresponding new quotient coordinate for
\(F_iH_j/(gh)\); this notation describes its intended equation and does not
assume division is available in \(P\).

The constructions take no unit-ideal hypothesis and assume no spectrum
identification, restriction map, or universal property. Both original tuples
may be empty, \(P\) may be the zero ring, and the coefficient valuation may be
trivial. No equality with a relative-series quotient is part of the definition.
The separate `IntersectionStatement` records the desired properties.

This is a derived product presentation motivated by Berkovich,
*Non-archimedean analytic spaces* (Trieste lectures, 2009), Exercise
2.2.2(ii)-(iii), printed/PDF p.9. The original gives rational quotient
equations and states closure under intersections. It does not prescribe
this finite-product indexing. Keeping all products, including \(f_i k_j\),
allows the generated ideal to be computed as the product of the two
original generated ideals. The Lean construction specializes to unit radii
and an enlarged Tate quotient; its statement retains explicit algebraic
unit-ideal hypotheses. The source's full affinoid-domain property and
relative-series comparison remain separate obligations.

The registered source is `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`;
the [author's PDF](https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf)
also gives the strict affinoid convention in Definition 2.1.2, p.7.
