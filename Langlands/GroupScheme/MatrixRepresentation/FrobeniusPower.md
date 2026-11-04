# Frobenius powers of finite matrix representations

This internal construction iterates the published actual matrix Frobenius
homomorphism. Over a field of exponential characteristic `p`,
`characteristicPowerMap k p A e` raises each element of a test algebra to
`p ^ e`, and `frobeniusPower` applies this operation to matrix entries of an
actual finite representation. Restriction commutes with the construction.

The affine matrix formula follows by induction on the number of iterations.
The universal character equation then shows that a character vector `v` of
weight `χ` becomes the coordinatewise power of `v`, of weight `(p ^ e) • χ`.
This holds on the coordinate algebra itself, including its nilpotents, rather
than only at rational points. In exponential characteristic one the construction
has no effect on matrix entries.

The provenance is the entrywise Frobenius operation used in Milne,
*Algebraic Groups* (2017), Lemma 5.16, printed p. 102 (PDF p. 118).
The explicit iteration, affine-coordinate formula and character-space interface
are derived implementation lemmas. This module constructs no smooth image and
asserts no general inverse-character occurrence.
