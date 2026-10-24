# Character transport under smooth duality and automorphisms

Author: Worker 51. The theorem `Langlands.characterTransport` proves the
published `Langlands.CharacterTransportStatement.{uG,uV}` with independent
group and representation-carrier universes and no extra assumptions.

Right translation of a test function controls the integrated operator on a
translated input by the finite-fiber integral change-of-variables theorem.
For a compact open subgroup of bi-invariance, the resulting equality shows
that every algebraic functional composed with the operator is fixed by that
subgroup in the contragredient action. Thus the entire algebraic transpose
image consists of smooth functionals. This step needs right measure invariance.
Left invariance together with inversion invariance supplies right invariance.

The existing smooth-dual pairing identity identifies the actual integrated
smooth-dual operator with the restriction of the transpose of the original
operator for the inverted test function. Full-image containment allows the
finite-rank transpose trace formula to prove equality of characters.
Compact-open cofinality, obtained from common compact-open bi-invariance for
the empty family, gives smooth-dual admissibility through the published
compact duality result.

For a continuous group automorphism preserving the chosen measure, change of
variables in the finite-fiber action integral identifies the actual pullback
operator with the original operator for the inverse-pulled test function.
Equality of finite-rank operators gives equality of traces. Published group
transport supplies admissibility of the actual pulled representation.

These two arguments give the exact conjunction target. They assert no
irreducibility, character separation, transpose invariance of distributions,
or Gelfand-Kazhdan equivalence.

The implementation follows the operator computations in Bernstein–Zelevinsky
(1976), Theorem 7.3, printed/PDF page 57, using the finite-rank character
defined in Section 2.17, printed/PDF page 21. Its more general locally profinite
form and explicit measure assumptions are those of the published target.
The argument is assembled from the actual algebraic integral, smooth-dual
pairing and finite-rank transpose trace constructions in the Library. It does
not use the ambient trace on an infinite-dimensional endomorphism space.
