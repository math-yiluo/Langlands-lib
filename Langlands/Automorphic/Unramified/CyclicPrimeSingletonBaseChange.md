# Unitary weak base change of singleton data

`CyclicPrimeSingletonBaseChangeReductionStatement F E` prepares the
constituent lifts used in Arthur–Clozel, *Simple Algebras, Base Change,
and the Advanced Theory of the Trace Formula* (1989), Chapter III,
Theorem 4.2(c), proof on printed p. 206. Given the Library's isobaric
formulations of parts (a) and (b), printed p. 202, it states that each
unitary cuspidal singleton over `F` has a unitary isobaric weak base
change to `E`. It assumes a prime-degree Galois extension of number
fields with compact adelic quotients.

`CuspidalOperatorRealization.hasUnitaryCentralCharacter_of_isUnitarizable`
first obtains the actual central Hecke character by irreducibility. The
action of a scalar from a finite local group is multiplication by the
corresponding character value. Invariance of the positive form on a
nonzero vector makes the norm of that value one. The kernel of the norm
of the idele character is closed and contains the principal ideles and
every finite local multiplicative group. The published idele subgroup
density theorem makes that kernel the whole idele group, so the
character has norm one on the idele-class group.

`cyclicPrimeSingletonBaseChange_of_cuspidal` obtains the norm-kernel
character from the cyclic norm theorem, since the Galois group has prime
order. It chooses an actual representative of the singleton's cuspidal
class and applies the central-character lemma to its given
unitarizability. The split is whether the norm-kernel determinant twist
fixes the class. The two inputs then supply either an upstairs singleton
or the upstairs multiset indexed by the full Galois group, with its
unitarity and actual weak base-change witnesses. The two lift cases are
explicit premises, and all four universes remain independent.
