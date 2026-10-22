# Proof of bounded descent through closed-ideal quotients

Author: Worker 36.

`Langlands.Analytic.boundedQuotientProperties` proves the separate proposition
`Langlands.Analytic.BoundedQuotientStatement`. The original module retains
its concrete `quotientMap`, `liftQuotient` and `quotientHomEquiv` interfaces.

For an actual closed ideal in a commutative normed algebra, `quotientMap`
is the algebraic quotient projection with bound one. An algebra homomorphism
annihilating the ideal descends by Mathlib's algebraic quotient construction.
The lemma `quotient_norm_bound` proves preservation of every positive bound C:
choose a representative whose norm exceeds the quotient norm by less than
epsilon/C. The bound on representatives then gives the same bound on the
quotient, by letting epsilon decrease to zero. `liftQuotient` applies this
lemma to the original map's bound to construct a bounded algebra map.

Surjectivity of the actual quotient projection proves uniqueness and the
equivalence between bounded maps out of the quotient and bounded maps on the
source annihilating the ideal. A bounded map annihilating an ideal also
annihilates its topological closure, because its zero fiber is closed by
continuity. The closing theorem combines this closure fact, unique descent,
and the general norm-bound lemma.

The source and target may be zero algebras, and their unit norms need not be
normalized. Completeness and ultrametricity are unnecessary. The proof uses
the continuous linear map underlying a bounded algebra map and Mathlib's
quotient norm. It does not use Tate evaluation or monomial convergence.

The source conventions and derived scope are documented in the paired
BoundedQuotient/Statement Markdown. The original is Berkovich's Trieste 2009
lectures, section 2.1's quotient-norm paragraph and Definitions 2.1.1–2.1.2,
p.7. No claim that all ideals are closed or that a quotient represents an
analytic domain is made.
