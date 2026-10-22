# Forward implications for association of cuspidal induction

Authors: Worker 72 and Worker 120. This pair separates the two forward
implications of Bernstein–Zelevinsky (1977), Theorem 2.9(a), for actual
general linear groups over finite extensions of p-adic fields. It contains
proposition definitions only.

`AssociatedCuspidalInductionHomTheorem` states implication (i) to (ii).
Association of irreducible cuspidal inducing representations gives an
actual nonzero intertwining map between their normalized inductions.

`TwoBlockAssociatedCuspidalInductionFactorsTheorem` states the two-block
special case of implication (i) to (iii), corresponding to the first step
of section 2.16. The hypothesis `B.length = 2` means that the source
standard Levi has two positive blocks. Association already requires the
actual source and target Levi subgroups to be permutation-conjugate.

`AssociatedCuspidalInductionFactorsTheorem` states implication (i) to (iii)
for any block count. The conclusion uses the published
`HaveSameJordanHolderFactors`: actual finite filtrations with irreducible
graded representations, a permutation of their indices, and actual
representation equivalences for matching factors. It retains multiplicity.
No finite-length or existence-of-series hypothesis is added.

All three targets quantify every prime, every actual p-adic field, every
compatible topological realization, and every positive rank, with independent
field and two carrier universes. The representations are smooth by their
`SmoothRep` types. Irreducibility and `IsLeviCuspidal` are hypotheses on
both inducing representations. The existing `RepresentationsAssociated`
predicate and the canonical `normalizedParabolicInduced` are reused.
The latter is the smooth right-translation representation on functions
covariant under the upper parabolic, twisted by its canonical positive
half-modulus. It unfolds to the induction expression in
`NormalizedCuspidalInductionStatement`; no arbitrary normalizing character
is introduced.

`CuspidalAssociationForwardTheorems` groups these separately accessible
targets. Its positive-rank scope does not replace or weaken
`CuspidalInductionAssociationTheorem`, whose rank-zero case and converse
implications remain separate proof obligations.

## Original source and proof boundaries

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), Theorem 2.9(a), printed page 448 (PDF page 9);
section 2.15(2), printed page 449 (PDF page 10); and sections 2.16–2.17,
printed pages 449–450 (PDF pages 10–11). Literature ID:
`bernstein-zelevinsky-1977-induced-i`. Original PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
These original pages were read directly on 2026-10-21.

The source derives the nonzero intertwiner from normalized reciprocity,
the associated Jacquet filtration, and the fact that a cuspidal constituent
is a quotient of a quasicuspidal representation. It derives equality of
factors first for two blocks using maps in both directions and the additive
Jacquet-length argument of section 2.14, then passes through elementary
maps using induction transitivity and exactness. Section 2.17 identifies
the elementary steps for general linear groups with adjacent block
transpositions. These are proof dependencies, not data assumed by any
target here. No proof of these implications is asserted by this pair.
