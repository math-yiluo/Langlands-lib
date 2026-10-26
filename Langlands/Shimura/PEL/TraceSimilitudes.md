# Algebraic and bilinear similitudes of the trace pairing

This internal construction identifies actual algebra-with-involution
similitudes with the left-algebra-linear similitudes of the trace form.
It retains the opposite group required by right multiplication and
preserves the multiplier.

## The algebraic comparison

Let R be a commutative ring and A an R-algebra. Let psi be a nondegenerate
R-bilinear form on A and sigma an R-algebra involution satisfying

    psi(xb,y) = psi(x,y sigma(b)).

The theorem `rightMul_similitude_iff` proves that, for a unit g of A and
a unit c of R, right multiplication by g is a psi-similitude with
multiplier c exactly when

    g sigma(g) = algebraMap(c).

For the forward implication, move g from the first argument to the
second using adjointness, set the second input to 1, and use right
nondegeneracy to deduce the displayed algebra identity. The converse
substitutes that identity and uses R-linearity.

Every A-linear automorphism e of the left regular module A satisfies
e(x) = x e(1). The unit `selfEquivUnit e` has value e(1) and inverse
e inverse(1); applying e and its inverse proves the two unit identities.
Thus `algebraicToBilinear` and `bilinearToAlgebraic` give the two maps of
`algebraicBilinearEquiv`.

The domain is sigma.similitudes opposite. If right multiplication by g
is composed after right multiplication by h, its value at x is x h g.
This reverses the product of the units. The scalar coordinate can be
kept unchanged because R is commutative. The equivalence proves both
inverse laws and the group product law, and
`algebraicBilinearEquiv_multiplier` proves that the recorded multiplier
is preserved.

These constructions require no field, dimension, or invertibility of
the group order; their inputs are the stated actual form, its
nondegeneracy and its adjoint identity.

## The actual trace-form specialization

`CentralSimpleUnitaryData.traceSimilitudesEquiv` applies this equivalence
to `tracePairing beta` and `tracePairingAdjoint beta hbeta`. The preceding
module proves the required nondegeneracy and right adjoint identity
from the actual normalized trace and skew unit beta. The specialized
equivalence sends an algebraic similitude (g,c) to the A-linear
automorphism x ↦ xg with multiplier c. Its action and multiplier formulas
are proved.

The provenance is internal: this is an intrinsic consequence of the
constructed trace pairing, its two adjoint actions, and the existing
algebraic and bilinear similitude subgroups. No identification is
assumed as an input. This file compares rational point groups in the
trace specialization. It does not construct a scheme isomorphism,
scalar-extension naturality or adelic continuity, or choose beta with
the positivity and signatures required for the final Harris PEL model.
