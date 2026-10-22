# Rational localization for arbitrary presented affinoid inputs

Author: Worker 36.

`RationalLocalization.LocalizationStatement` quantifies over every
complete ultrametric normed field `K`, every presented strict affinoid
algebra `P`, and actual elements `g` and `f_j` of `P`. The construction
in `Definitions` supplies the quotient, bounded base map and new
coordinates. The proposition has five clauses:

1. The new coordinates satisfy `baseMap(g) Y_j = baseMap(f_j)`.
2. Every point of the quotient spectrum restricts to the rational
   inequality locus in the base spectrum.
3. If `g` and the `f_j` generate the unit ideal in `P`, the image of
   `g` is invertible, the spectrum image is exactly the rational locus,
   and the spectrum map is a closed embedding. Under the same
   hypothesis, bounded algebra maps from the quotient to any normed
   algebra agreeing on the base are equal. This last target need not
   be complete or ultrametric.
4. A bounded map from `P` to a complete ultrametric normed algebra,
   together with a tuple of uniformly bounded monomials satisfying
   the denominator equations, extends to a bounded map from the
   constructed quotient. Both its base restriction and all new
   coordinate values are prescribed. This clause needs no unit-ideal
   hypothesis; with that hypothesis the previous clause gives uniqueness.
5. A bounded equivalence of input algebras carrying `g` and `f_j` to
   their counterparts induces a bounded quotient equivalence. It
   respects the base maps and new coordinates, and its contravariant
   spectrum homeomorphism commutes with the base spectrum
   homeomorphism. The two presentations can have different arities.
   This clause also needs no unit-ideal hypothesis.

The extension targets live in an independent universe. Empty numerator
tuples, zero algebras, and trivially valued fields are permitted.
The equivalences are bounded in both directions, not asserted to
preserve norms isometrically.

This is a derived reformulation of the presentation-level targets
using genuine affinoid-algebra elements. Recovering the original
presentation from its closed ideal and choosing preimages under the
surjective quotient map supply the input conversion. The intended
proof transports the quotient, spectrum and bounded-map results through
the constructed model equivalence. It does not assume their desired
outputs.

Original context is Berkovich, *Non-Archimedean analytic spaces*
(Trieste 2009), Definition 2.1.11 on printed page 8, Definition 2.2.1
and Exercise 2.2.2(ii) on page 9, and Fact 2.2.3(i) on page 10.
The original rational domain uses relative series, arbitrary positive
radii and absence of common spectrum zeros. The target here uses
unit radii, the enlarged Tate quotient, and explicit algebraic
unit-ideal generation. It retains the bounded-monomial premise for
extension. Relative-series comparison, the implication from no common
zeros to unit-ideal generation, arbitrary radii, and factorization
based solely on containment of a spectrum image remain separate.
In particular this is not yet the full analytic-domain property.

Registered original: `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
