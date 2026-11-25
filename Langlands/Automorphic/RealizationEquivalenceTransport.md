# Transporting equivalences of operator realizations

This module proves that full operator equivalence passes to complex
conjugates and to common Hecke determinant twists, and that an operator
realization is equivalent to its double conjugate. The complex-linear
equivalence of the conjugates composes the original equivalence with an
antilinear identification on each side. The double conjugation equivalence
composes the two antilinear identifications and applies
`operatorConj_operatorConj`. The twist equivalence transports the original
linear equivalence along the two published determinant-twist maps. In each
case the published operator-action formulas prove intertwining for the
whole operator algebra.

These internal lemmas implement the passage from equivalent unitary parts
with equal twisting exponents to equivalent original cuspidal representations
in Jacquet–Shalika II, proof of Theorem 4.2, printed p. 807 (PDF p. 32),
after display (7).
