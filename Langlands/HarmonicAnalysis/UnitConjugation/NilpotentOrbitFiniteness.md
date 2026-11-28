# Finiteness of nilpotent conjugacy classes in a semisimple ring

`NilpotentOrbitFinitenessStatement` says that a semisimple ring \(R\) has
a finite set of nilpotent elements such that every nilpotent element is
of the form \(uNu^{-1}\) for a representative \(N\) in that set and
a unit \(u\) of \(R\). `nilpotentOrbitFiniteness` proves the statement.
In particular the Lie algebra of the unit group of a finite-dimensional
semisimple algebra has finitely many nilpotent orbits. This is the
finiteness property used in Harish-Chandra, *Admissible invariant
distributions on reductive p-adic groups*, ULS 16 (1999),
Introduction, p. 3 (PDF p. 18), and in the setting of Lemma 3.3.

For a nilpotent endomorphism of a \(d\)-dimensional left vector space
over a division ring, stabilization of the kernels of the powers shows
that the \(d\)-th power is zero. Its ranks through exponent \(d\) take
values from \(0\) to \(d\). The proof chooses a nilpotent endomorphism
for each realized list of these ranks. The conjugacy criterion in
`NilpotentEndomorphismConjugacy` intertwines any nilpotent with the
representative of its list, and a linear automorphism is a unit of the
endomorphism ring.

`matrixRingEquivEndVecMulOpposite` identifies a matrix ring over a
division ring with the opposite of the endomorphism ring on a left
vector space. Passage to the opposite preserves nilpotence and
transports conjugacy by passing to the inverse conjugating unit in
the opposite. Products of the representative sets give representatives
for a finite product of rings, using the product of the conjugating
units. A sum of the vanishing exponents of the components provides
a common vanishing exponent for each representative in that product.
The Wedderburn–Artin ring isomorphism transports the result to \(R\).
