# Proof of left-translation compatibility for the enveloping action

The theorem `envelopingLeftTranslation` proves the exact proposition
`EnvelopingLeftTranslation` for every number field and natural rank.

First, tensor induction extends the already proved real directional
translation identity to the complexified Lie action. On a pure tensor the
claim is a complex scalar multiple of the real identity; addition follows
from linearity and distributivity.

Every element of the universal enveloping algebra has a representative in
the tensor algebra, by surjectivity of the defining ring-congruence quotient.
Tensor-algebra induction reduces commutation to scalars, Lie generators,
products and sums. Scalars commute by the complex-algebra law. The generator
case uses the complex Lie identity and the exact generator formula.
Associativity and distributivity handle products and sums.

The evaluation corollaries give D(u)(L(a)f)(x) = D(u)f(ax). Consequently
D(u) preserves any specified left-translation invariance of f. Restriction
along the actual center inclusion gives the same compatibility for the
center action.

This is an internal proof of the derived proposition described in the paired
statement Markdown. It uses the constructed actual operators throughout.
No new source theorem, Lie-action hypothesis or finiteness assertion is used.

The final unapplied-constant assignment checks the complete declaration
telescope, including the field instances and rank, against the target.
