# Rational intersection and bounded restriction target

Author: Worker 36.

`Langlands.Analytic.RationalIntersection.IntersectionStatement` is a
proposition about the concrete product construction in `Definitions`.
It quantifies over every complete ultrametric normed field \(K\), presented
strict affinoid \(K\)-algebra \(P\), finite lengths \(m,n\), denominators
\(g,h\), and actual numerator tuples \(f,k\).

Assume each original denominator together with its numerator tuple generates
the unit ideal in \(P\). Write \(F=(g,f)\), \(H=(h,k)\), and let \(C\) be the
constructed rational quotient with denominator \(gh\) and all products
\(F_iH_j\) as numerators. The five conclusions are:

1. The combined denominator and numerator tuple generate the unit ideal.
2. Their rational inequality locus is exactly the intersection of the
   original two rational inequality loci.
3. The spectrum pullback along the constructed bounded map \(P\to C\) has
   range equal to that intersection.
4. That spectrum pullback is a closed embedding.
5. There exist bounded \(K\)-algebra maps from each original rational
   localization to \(C\), whose compositions with the original base maps
   both equal the constructed map \(P\to C\).

The last clause asserts existence and the commuting equations. It does not
assert uniqueness of those maps or a pushout property. All conclusions are
under the two unit-ideal hypotheses, while constructing \(C\) requires neither.
There are no nontrivial-valuation, nonzero-ring, positive-tuple-length, or
nonempty-intersection hypotheses. Spectrum pullback is contravariant, so
the algebra maps in the last clause induce maps from the intersection
spectrum to the two original localization spectra.

This target is a derived unit-radius part of Berkovich,
*Non-archimedean analytic spaces* (Trieste lectures, 2009), Exercise
2.2.2(ii)-(iii), printed/PDF p.9, with the spectrum identification of
Fact 2.2.3(i), p.10. The source states the stronger result that intersections
of rational domains are rational domains. Here the product construction
uses one enlarged closed-ideal Tate quotient and assumes algebraic
unit-ideal generation. It does not identify that hypothesis with absence of
common spectrum zeros. It does not establish the image-containment
factorization of Definition 2.2.1, compare to the source's relative-series
quotient, treat arbitrary radii, construct sheaves, or glue an analytic atlas.

The proof is separate. This statement imports the concrete definitions only;
neither spectrum realization nor bounded restriction maps are input data.
The product tuple and its unit-ideal conclusion are explicit algebraic
content, and the range, embedding, and map-existence clauses are assertions
about the constructed quotient.

The registered original is `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`;
see the [author's PDF](https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf).
