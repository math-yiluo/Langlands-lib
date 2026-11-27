# Prime power generators on finite-constant affine curve charts

`exists_primePowerGenerator` takes a height-one prime \(P\) of a
Dedekind domain with finite class group. The order of the class group
annihilates the ideal class of \(P\). A generator of that positive
power of \(P\) is nonzero and belongs to \(P\). If it belonged to a
second height-one prime, the inclusion of the power would imply an
inclusion of primes. The two primes would be equal by maximality.

`finite_classGroup_normalizedCurveChart` obtains the finite class
group for the normalized chart of a transcendental parameter \(s\)
over finite constants \(k\), when the function field \(F\) is finite over
\(k(s)\). Polynomial evaluation identifies \(k[X]\) with \(k[s]\).
The chart is finite over \(k[s]\) and torsion free over \(k[X]\), so
it has a finite free basis. The admissible polynomial absolute value
and this basis give the conclusion by Mathlib's
`ClassGroup.fintypeOfAdmissibleOfAlgebraic`. This argument uses the
finite normalized chart construction for inseparable as well as
separable field extensions.
