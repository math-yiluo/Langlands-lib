# Extreme orbit lines separated under the torus centralizer

This internal construction works over any infinite field and for any abstract group
representation on a finite coordinate space. The supplied torus parameters act by
an actual simultaneous diagonalization with integral weights. The projective orbit
is closed in the homogeneous-equation sense of `FlagCore.IsClosedOrbit`.

`centralizerSeparatedOrbitLines` takes a nonzero base vector and a nonfixed orbit
line, and chooses two actual group representatives. Both orbit lines are fixed by
every torus parameter. No point commuting with every torus parameter can send the
second vector to a scalar multiple giving the first vector. No centralizer
containment in a stabilizer is assumed.

The proof separates the finitely many occurring weights by an integral
cocharacter and contracts at its minimum and maximum levels. The levels differ:
otherwise the original line would be fixed. The two contracted vectors are
eigenvectors for the same cocharacter, with different integer exponents. A point
commuting with the torus preserves its eigenvalues. A scalar proportionality would
therefore make the two power maps equal on all field units. Over an infinite
field, the existing `eq_of_forall_zpow_eq` forces equal integer exponents, a
contradiction. Cancellation uses the nonzero first orbit vector.

The construction derives from `FlagCoreLinear`, particularly its separating
cocharacter, lowest-weight contraction, fixed-line, and power-map lemmas. This is
a strengthening of the two-line argument used in `TorusFixedOrbitLines`; it
retains separation under the whole torus centralizer. It does not construct a
proper homogeneous quotient or prove rank-one positive-root uniqueness.
