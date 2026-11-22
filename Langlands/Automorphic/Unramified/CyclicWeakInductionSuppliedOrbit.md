# Unique-place supercuspidality from strong matching of the supplied weak induction

`CyclicWeakInductionOrbitProductLiftAtUniquePlaceStatement` expresses the
orbit-product identity for the given cuspidal weak induction `S` of `T`.
It assumes a prime-degree cyclic extension of number fields, a unique finite
place upstairs, unitary central characters, and an irreducible admissible
downstairs component of the given presentation. The upper cusp is regular
under the global Galois action and has a supercuspidal component at the upper
place. The identity compares the two supplied local actions. The normalized
product of the entire orbit of the upstairs action must be the sigma-lift
of the downstairs action for the extended generator of the actual completion
extension.

Henniart (2012), §1.1, printed p. 2 (PDF p. 3), gives the cofinite Euler-factor
identity. Section 1.10, printed p. 5 (PDF p. 6), defines global induction by
this identity and invokes rigidity to identify any supplied induction.
Theorem 3(i) gives its global orbit product, Theorem 4 identifies the local
component of base change, and Theorem 6(i) gives the corresponding local
orbit formula at the unique place. Section 1.11, printed p. 6 (PDF p. 7),
formulates local base change by the Shintani identity. Henniart–Lemaire (2011),
II.2.9, printed p. 69 (PDF p. 77), relates this identity to the sigma-lift
defined by concordant test functions.

`CyclicWeakInductionSupercuspidalFromSuppliedOrbitStatement` takes that strong
comparison, `CuspidalSigmaLiftExistenceStatement` and
`SigmaLiftGenericFibreStatement` as premises. Arithmetic transport turns the
distinct local conjugates into global regularity and a trivial stabilizer at
the upper completion. The weak Euler identity and unitarity of the upper
central character give unitarity of the supplied downstairs cusp.
An irreducible admissible finite slice then gives a genuine spectral
presentation of that cusp, with the component carriers put in the required
universe. The genericity theorem supplies a Whittaker datum at the actual
base completion.

The local implication in `CyclicInductionSupercuspidalCompletion` applies
the two sigma-lift results to the matched orbit product. It identifies the
downstairs component with a norm-trivial twist of a supercuspidal witness.
The resulting component belongs to the presentation of `S` itself. The two
theorems give the conditional unrestricted and totally complex conclusions,
each with the four independent universes and positive ranks of the published
targets.

The local premises come from Henniart–Lemaire (2011), II.4.12 Remarque,
printed p. 97 (PDF p. 105), and II.4.8 Lemme (2), printed pp. 90–91
(PDF pp. 98–99). The resulting local implication supplies the supercuspidality
step of Henniart–Herb (1995), Proposition 5.5, printed pp. 152–153
(PDF pp. 22–23).
