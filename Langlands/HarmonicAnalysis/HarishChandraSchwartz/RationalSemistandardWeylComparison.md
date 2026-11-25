# Intrinsic Weyl comparison at an actual inducing representative

This adapter transports a displayed comparison in the dynamic coefficient
model to the intrinsic product-induced coefficient objects of the actual
semistandard spectral families.
Both parabolic presentations use the same compact, with the displayed
Iwasawa factorizations. The target centralizer equality is the all-test
conjugation equality for the specified actual Weyl lift.

The intrinsic inducing object is pulled back along the identity between
its literal Levi and the dynamic Levi. The dynamic parameter is the unit
character with this inducing object as base. The actual twist-by-one
isomorphism and the identity round trip identify the source with the
original intrinsic inducing object. On the target side the actual unitary
conjugate-twist isomorphism first identifies the twist with the conjugate
pullback. The two changes of Levi presentation compose with that pullback
as the literal inverse-conjugation action of the Weyl representative.
The composite uses the published composition isomorphism of conjugation
functors and the two equalities of literal Levi subgroups.

`comparisonAtOne` transports the displayed ambient intertwiner by these
source and target equivalences and by the existing product normalization.
This is a map between the actual VI.1 coefficient fibers for the original
representative and its intrinsic conjugate. The supplied comparison carries
its given compact and scale through the equivalences. The later section
target uses this adapter together with the certificate for the V.3 standard
tensor at the fixed maximal split torus, its adapted compact and the
trace-normalized quotient Weil measure.
