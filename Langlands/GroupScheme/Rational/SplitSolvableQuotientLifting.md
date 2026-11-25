# Rational lifting for quotients by split-solvable groups

This internal helper implements the rational lifting step in the proof of Milne, *Algebraic Groups* (2017), Theorem 17.105(a).

For a smooth surjective quasi-compact homogeneous quotient by a closed split-solvable subgroup, every rational quotient point lifts to a rational group point. The supplied fiber criterion identifies the differences of local lifts with points of the subgroup on every relative test scheme.

The proof pulls back the quotient along the rational point. The differences of its tautological lifts define a subgroup-valued cocycle. The split-series field-cocycle theorem trivializes this cocycle, and multiplying the lifts by the resulting cochain gives a compatible group point. Effective epimorphism descent produces the rational representative. The fiber criterion verifies that its quotient is the specified rational point.
