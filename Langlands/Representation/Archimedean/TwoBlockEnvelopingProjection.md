# Parabolic projection of the complex matrix center

This module constructs the enveloping algebra projection used by
Harish-Chandra (1968), Chapter I, §6, printed pp. 19–20 (PDF pp. 29–30)
for two-block constant terms.

The linear projection retains the PBW monomials supported in the
diagonal blocks. It sends a retained monomial to the corresponding word
in the Levi enveloping algebra and is a left inverse to the Levi
inclusion. Products with an upper radical generator on the left vanish
under the projection. In PBW coordinates left multiplication by such
a generator increases its exponent in the upper prefix, since those
generators commute.

The span of those products is stable under right multiplication by
ambient operators and left multiplication by Levi operators. The
commutator of a Levi matrix unit with an upper radical matrix unit is a
linear combination of upper radical matrix units. The proof extends this
calculation to the full Levi enveloping algebra.

The grading decomposition gives the congruence of each central operator
with its projected operator modulo the upper radical span. The stability
properties give the center and multiplication rules for
`blockLeviCenterProjection`. The ordinary diagonal Harish-Chandra
polynomial functional also kills the span, using the zero character on
strictly upper triangular generators.
