# Adjoint lattice exactness

`Langlands.BushnellKutzko.adjointExactness` proves
`Langlands.BushnellKutzko.AdjointExactnessStatement` in its three
independent universes. The source is C. J. Bushnell and P. C. Kutzko,
*The admissible dual of GL(N) via compact open subgroups* (1993),
registered as `bushnell-kutzko-1993-admissible-dual-gln`. The target
covers the lattice intersection in (1.4.4), the critical exponent in
(1.4.5)–(1.4.6), and the four exact sequences in (1.4.7) and (1.4.10),
printed pp. 36–38 (PDF pp. 48–50).

The proof chooses a base uniformizer and obtains the period and
denominator-clearing formulas from `AdjointLatticeBounds`.
`RelativeFiltrationInversion` proves relative inversion using a
splitting basis over `E`. `AdjointLatticeLifting` then gives critical
nonemptiness and the integral lifting step. Boundedness and nonemptiness
give a greatest integer in the critical set. Since the generator is
nonscalar, the defining `WithBot` exponent is the coercion of this
greatest integer. At any depth at least this exponent, all larger
integers lie outside the critical set, as required by integral lifting.

The order-image property supplies an order element whose corestriction
is the relative identity. Relative linearity and multiplication of a
relative filtration step by the order then identify the image of each
endomorphism step with its intersection with the centralizer. The
global image–kernel equality in `AdjointCentralizer` puts each element
of the corestriction kernel in the commutator image. Integral lifting
then produces a preimage at the required depth.

For the quotient sequences, a representative whose corestriction lies
in the right denominator has the same corestriction as an element of
the middle denominator. Subtracting this element gives a commutator
that has a lift in the specified mixed adjoint lattice. The first map
carries both the numerator and denominator into their specified
lattices, and its preimage of the middle denominator in the left
numerator is the left denominator. The corestriction maps onto both
right lattices, proving surjectivity on the quotient. For an
unquotiented middle term, the left denominator is the relative step.
The mixed lattice at preimage depth zero is the adjoint lattice.
At depth `m` it is the product of the relative step and the adjoint
lattice. These identifications give the displayed lattices and both
maps in the published proposition.
