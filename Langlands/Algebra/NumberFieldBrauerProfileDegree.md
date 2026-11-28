# Prescribed-degree central simple representatives of number-field profiles

Over a totally complex number field, `exists_csa_degree_with_finiteRelativeInvariants`
realizes a finitely supported zero-sum profile killed by a positive integer `n`
by an actual central simple algebra of dimension `n * n`. The values are
read on the actual finite completions using the supplied invariant family
`I` and the global Galois splitting chart. The family must satisfy, at
every prime `p`, both `RelativeClassFormation` and
`ArithmeticNormalization`; these are hypotheses of the statement. They
are essential: an `InvariantFamily` is only a family of additive maps,
and for the family with all maps zero every value is zero, so no nonzero
profile could be realized.

The relative profile construction first supplies a central simple
algebra with the required values. By injectivity of the relative
invariants (`RelativeImages`, part of `RelativeClassFormation`), the
local classes at the supported places are annihilated by `n`, and the
other finite algebras split.
Choose an extension of degree `n` with local degree `n` at all
places over the support. Scalar extension multiplies the local
Brauer invariant by that degree, so the algebra splits over the
upper finite completions. The infinite completions are algebraically
closed. The number-field splitting theorem then gives a global
matrix chart over the degree-`n` extension.

Over the original field, the division component has the same
Brauer class and splits over the same extension. Its matrix splitting
size divides `n`. Taking matrices over that component gives degree
`n` without changing the Brauer class. A common Galois splitting
field then gives the same relative chart class and all the same finite
values for the new representative.

This internal assembly uses the Library's relative profile lift,
local scalar-extension invariant, global splitting theorem, and
division splitting degree bound.

## Period and index over totally complex number fields

`NumberFieldTotallyComplexBrauerPeriodIndexStatement` states that the
additive order of the Brauer class of a finite-dimensional central
division algebra over a totally complex number field equals its
reduced degree. The theorem `numberFieldTotallyComplexBrauerPeriodIndex`
proves it in every universe.

The determinant of the scalar defect shows that the period divides the
reduced degree, so the period is positive. The Brauer class at every
finite completion is killed by this period. The proof applies the
splitting-field construction above with the finite set of nonsplit
places and with the period as the prescribed degree. The reduced
degree of the division algebra divides the degree of this splitting
field. The two divisibilities give equality.

Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994),
§1.5.1, printed p. 38, give the exponent–index equality over number
fields as a consequence of Theorem 1.12 and the Grunwald–Wang theorem.
The Lean proof in the totally complex case uses prescribed finite
completion degrees and Brauer–Hasse–Noether splitting.
