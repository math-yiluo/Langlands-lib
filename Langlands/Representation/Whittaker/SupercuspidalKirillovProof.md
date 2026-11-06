# The supercuspidal Kirillov model

Author: Worker 1740. The final entrywise conversion of a test function to the
compact model adapts the published proof by Worker 127 in
`WhittakerTypeKirillovProof.lean`.

`Langlands.supercuspidalKirillov` proves the unchanged Library proposition
`Langlands.SupercuspidalKirillovStatement.{uF,uV}`. It covers every prime,
every supplied p-adic field with its canonical topology, every natural `n`,
and every irreducible supercuspidal complex representation of
`GL_(n+1)(F)`. The field and vector-space universes are independent.

For every continuous nontrivial unitary additive character, the theorem gives
a nonzero standard Whittaker functional. For every such functional, all its
coefficients have the target's covariance, open right stabilizer, and compact
support modulo the upper unipotent subgroup on actual mirabolic matrices.
Every function satisfying those three conditions agrees on the mirabolic
subgroup with the coefficient of exactly one vector. Values away from that
subgroup are not constrained by this realization.

## Implemented argument

The auxiliary declarations are in
`Langlands.Whittaker.SupercuspidalKirillovProof`. They are internal deductions
from the imported results, not additional assumed statements.

`lower_restriction` identifies each lower derivative of the mirabolic
restriction with a vanishing supercuspidal derivative.
`detect_subquotient` uses exactness to carry each actual subquotient into
a subquotient of that zero derivative. If the top derivative also vanishes,
the published mirabolic derivative detection theorem makes the subquotient
itself zero.

`irreducible_of_derivatives` applies the exact top derivative functor to
`S → X → X/S` for every invariant subspace `S`. The top derivative of `X`
has dimension one and is irreducible. If the derivative of `S` is zero,
subquotient detection gives `S = 0`. Otherwise its injection into the top
derivative of `X` is surjective, so the derivative of `X/S` is zero, giving
`S = X`. The top derivative also detects that `X` is nonzero. This argument
does not require a finite-length premise.

`irreducible_restriction` applies this criterion using
`SupercuspidalDerivativesProof.finrank_generalLinearDerivativePositive_top`.
Explicit equality transport aligns the ranks `n` and `0+n`; it changes
neither the representation nor the hypotheses.

`exists_functional_zero` chooses a nonzero dual vector on the nonzero top
derivative and pulls it back along the surjective `topQuotient`.
`comp_topQuotient_mem_glFunctionals` supplies equivariance, and surjectivity
preserves nonvanishing. `exists_functional` transports this result to the
rank convention of the target.

For an arbitrary nonzero Whittaker functional, `mirabolicCoefficientMap`
is a nonzero intertwiner out of the irreducible mirabolic restriction, hence
is injective. `range_eq_mirabolicCompact`, using the published compact
minimality theorem and a compact local section nonzero at the identity,
identifies its image with `mirabolicCompactSubrepresentation`. In particular,
every coefficient has compact projected support.

`ambient_compact_support` uses
`QuotientIntegration.leftQuotient_exists_isCompact_image` for the closed
upper unipotent subgroup of the locally compact mirabolic group. A compact
set of representatives maps continuously into the ambient general linear
group. Equality of left cosets supplies the factorization `q = u*c` required
by the target's support predicate.

The final theorem packages the given additive character with
`UnitaryAdditiveCharacter.ofComplex`; its complex values are unchanged.
`mem_glFunctionals_iff_entrywise` and `standardCharacter_eq_product` give the
exact adjacent-entry product convention in the target. Smoothness of the
original representation gives an ambient open subgroup fixing each vector.
For surjectivity, `mirabolicCompactRestriction` converts a target test
function into the compact model, whose inclusion in the coefficient image
gives a realizing vector. Injectivity of the coefficient map proves its
uniqueness.

All topological and local compactness instances used in the final assembly
come from the field's canonical topological data. No hypotheses are added,
and the target Lean/Markdown pair and its imports are unmodified.

## Original sources and provenance

- Bernstein and Zelevinsky, *Representations of the group GL(n,F) where F
  is a non-Archimedean local field* (1976), Proposition 5.15 and
  Theorems 5.18–5.19, printed pp.49–50.
  Registered source: `bernstein-zelevinsky-1976-representations-gln`;
  SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Bernstein and Zelevinsky, *Induced representations of reductive p-adic
  groups I* (1977), §§3.2–3.5, printed pp.451–452, for the exact derivative
  and filtration framework. The supercuspidal top derivative input is the
  published proof of §4.4 in `SupercuspidalDerivativesProof`.
  Registered source: `bernstein-zelevinsky-1977-induced-i`;
  SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions*
  (1983), §2.2, printed p.386, for the compact mirabolic model and its equality
  with the restriction for supercuspidal representations.
  Registered source: `jpss-1983-rankin-selberg`;
  SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

The implemented route combines the existing derivative and compact-minimality
proofs rather than reproducing the original compact induction construction.
The short exact sequence criterion and the ambient support adapter are
derived implementation lemmas explained above.
