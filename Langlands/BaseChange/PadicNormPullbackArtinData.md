# The finite Artin presentation of a norm pullback over p-adic fields

The theorem supplies `CyclicNormPullbackArtinData` for finite abelian
extensions of p-adic fields whose carriers lie in the same universe,
with the indicated supplied topologies and valuations. It first
replaces the quasicharacter by a finite-order character on integral
units, preserving the conductors of twists and of the norm pullback.
A common finite abelian Galois extension contains the upper field and
kills the finite-order character on norms. Reciprocity lifts that
character to the finite Galois group.

The norm square identifies norm-trivial twists with the characters of
the quotient by the relative Galois group. Pullback along the geometric
Artin map yields each continuous twist character and compares its
conductor with its finite Artin expression. The norm square makes the
norm pullback correspond to restriction of the finite Galois character.
Restricting scalars identifies the lower groups and fixed spaces used
in the relative conductor calculation. The p-adic tower identities
supply the residue-degree and different-order formulas at a cutoff of
the lower filtration.

The reciprocity, norm-subgroup existence, and unit-image comparisons
use the class-field-theory conventions of Serre, *Local Fields* (1979),
Chapter XI, §3, Chapter XIV, §6, and Chapter XV, §2. The Lean proof
uses geometric reciprocity throughout. Inverting the arithmetic symbol
preserves its kernel and its image subgroups.
