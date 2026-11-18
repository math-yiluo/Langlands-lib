# Rational conjugacy of geometric Borels over finite fields

Worker 308, with the point and transport helpers of Worker 881.

This internal proof module supplies rational conjugacy of geometric Borel
subgroup ranges for the proof of the unchanged
`Langlands.GroupScheme.FiniteFieldBorelPairStatement`.

`exists_eq_inv_mul_rationalConjugate` expresses the published Lang equation
using the coefficient-conjugation action on the actual algebraic-closure
pullback. The coefficient equivalence transports the equation and its solution.

The Borel conjugacy lemma first applies geometric Borel conjugacy. Frobenius
invariance of the two original-field subgroups implies that the discrepancy
between the conjugator and its Frobenius translate normalizes the source
Borel. The published Borel normalizer theorem places the discrepancy in that
Borel. Lang's theorem there corrects the conjugator to a Frobenius-fixed
point, which the exact point-descent helper recovers over the original field.
Fpqc reflection gives equality of the original subgroup functors on all
tests.

The argument is derived from Milne, *Algebraic Groups* (2017), Proposition
17.99, pp.383–384, source `milne-2017-algebraic-groups`. The full proof uses
Lang correction in a Borel, then
[pair assembly](FiniteFieldBorelPairAssembly.md) applies rational conjugacy of
maximal tori in that solvable group. The
target statement's Markdown records the source proof's orientation and
stabilizer corrections. No reductivity hypothesis is added.
