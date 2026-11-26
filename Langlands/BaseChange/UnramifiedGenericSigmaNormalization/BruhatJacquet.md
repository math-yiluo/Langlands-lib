# The canonical action on the principal-series Jacquet quotient

`principalIntertwiner_jacquet` proves the identity on the actual Borel Jacquet
quotient of `principalSeriesOfTuple E z`. This is the identity used by
Henniart–Lemaire in the proof of I.5.4, Lemma 2, printed p. 35 (PDF p. 43).
The proof here uses restriction to the upper-unipotent orbits of the Borel
coset space and the quotient integral on each orbit. See the source details
in the [normalized σ-action statement](../UnramifiedGenericSigmaNormalizationStatement.md).

`Whittaker.unipotentOrbit` orders the orbits with open initial unions and
permutation representatives. Each representative is fixed by the entrywise
automorphism. Consequently the pullback preserves the support in each initial
union. The Borel coset space is compact, so a smooth induced section lies in
the compact induction model used for the support filtration.

Restriction from an initial support to its last orbit is surjective, with
kernel the preceding support. The restriction of pullback is precomposition
on the upper unipotent group. The compatible quotient measure for the orbit
stabilizer is invariant under this precomposition. Indeed, the ambient and
stabilizer Haar moduli are both positive and have a positive integral power
equal to one, by the finite order of the automorphism. The Library's compact
coinvariant integral identifies the orbit coinvariants with the corresponding
inducing coinvariants. Equality of integrals gives equality of the two
restricted section classes.

By right exactness of coinvariants, the difference of a section and its pullback
has a class represented in the preceding support. Induction down the finite
support filtration shows that a power of the descended operator minus the
identity kills each class. Pullback has finite order on sections and on their
classes, so the characteristic-zero periodic-vector lemma fixes every class.
`borelCoinvariantsEquiv` identifies the Borel quotient with the full
upper-unipotent coinvariants by sending the class of each vector to the class
of the same vector.
