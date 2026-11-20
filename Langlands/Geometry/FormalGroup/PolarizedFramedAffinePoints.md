# Polarized framed triples on affine Nilp tests

Harris, *Supercuspidal representations in the cohomology of Drinfel'd
upper half spaces* (1997), Appendix, printed p. 113 (PDF p. 39),
specifies an integral polarized object and a rigidifying quasi-isogeny
on its special fiber. The rigidifier is order-linear and respects the
polarizations up to a constant in \(\mathbf Q_p^\times\).
Rapoport–Zink, *Period Spaces for p-divisible Groups* (1996),
Definition 3.21, printed pp. 81–82 (PDF pp. 95–96), use the same
direction for the quasi-isogeny from the fixed frame to the target.

`PolarizedFramedAffinePoint` constructs these affine triples for a
specified polarized frame over the residue quotient of the
coefficient ring. The test algebra is in `Nilp`. The framing source
is extension of the frame to the actual quotient of the test
algebra. The target is the actual coefficient reduction of the
polarized coordinate law. The rigidifier is a section of their
rational Hom sheaf, commuting with the actual order endomorphisms.
The existence of a single \(p\)-adic multiplier imposes the
denominator-cleared pairing condition on the actual torsion kernels.
Its numerator witnesses supply the local quasi-isogeny.

An isomorphism of triples is an actual polarized integral isometry
whose reduction intertwines the two framing sections. Identity,
inversion and composition prove the equivalence relation used in
`IsomorphismClass`.

The construction uses arbitrary order data and a single finite
coordinate system for each affine target. It supplies the
polarized framing conditions before imposing the split special
condition of the particular Drinfeld moduli problem.
