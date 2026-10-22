# Bounded pushout target for the rational intersection quotient

Author: Worker 36.

`Langlands.Analytic.RationalIntersection.BoundedPushoutStatement` asserts a
bounded pushout property for three actual constructed rational algebras.
Let \(P\) be a presented strict affinoid algebra over a complete ultrametric
normed field \(K\), and suppose each of \((g;f_i)\) and \((h;k_j)\) generates
the unit ideal. Write \(A_f,A_k\) for their rational localization algebras,
and \(C\) for the product-denominator intersection quotient constructed in
`RationalIntersection/Definitions`.

The statement asserts existence of bounded \(K\)-algebra maps
\(L:A_f\to C\) and \(R:A_k\to C\) whose composites with the two structural
maps from \(P\) equal the constructed structural map \(P\to C\).
For every complete ultrametric normed commutative \(K\)-algebra \(B\) and
bounded maps \(\alpha:A_f\to B\), \(\beta:A_k\to B\) that agree on \(P\),
there exists exactly one bounded \(K\)-algebra map \(\psi:C\to B\) satisfying
\(\psi L=\alpha\) and \(\psi R=\beta\).

The coefficient field and the common target have independent universes.
The target need not be affinoid, need not have a normalized unit norm, and
may be the zero ring. The original tuple lengths may be zero, the base
algebra may be zero, and the field's valuation may be trivial.
Neither restriction maps nor an extension operator are supplied as input;
their existence and the stated uniqueness are conclusions. Boundedness
means the existing positive-constant norm bound, not contractivity.

This is a derived algebraic consequence of the concrete rational quotient
and bounded evaluation constructions. Its source context is Berkovich,
*Non-archimedean analytic spaces* (Trieste lectures, 2009), Exercise
2.2.2(ii)-(iii), printed/PDF p.9: the rational quotient equations and
closure of rational domains under intersections. The common-target
formulation for arbitrary complete ultrametric normed algebras is an
internal derived target, rather than a separate theorem quoted from that
source.

The construction uses unit radii, an enlarged closed-ideal Tate quotient,
and explicit unit-ideal hypotheses. No implication from spectral bounds
to power bounds, inverse from spectral nonvanishing, or
image-containment factorization of Definition 2.2.1 is asserted here.
Comparison with the source's relative-series quotient, arbitrary radii,
and structure-sheaf descent remain separate obligations.

The registered original is `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`;
see the [author's PDF](https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf).
