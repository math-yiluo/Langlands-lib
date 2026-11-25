# Affine center surjectivity from faithful norms on finite-type domains

This helper module is used by `AnalytificationCenterProof`. It proves
reductions toward clause (1)
of `Langlands.Analytic.SchemeAnalytification.AnalytificationCenterStatement`.
The reductions retain the seminorm range property and the existence of faithful
extending norms as explicit hypotheses. They do not prove that clause
unconditionally.

`PrimeQuotientNormData K A` is the explicit interface asserting that every prime
quotient of `A` has a multiplicative seminorm extending the norm of `K` with zero
kernel. The definition supplies no existence proof. The lemmas show how to use
this input to prove surjectivity of the affine center, and how a norm-extension
theorem for all finite-type domains would supply it.

## Provenance

The interface and conditional reductions are internal derived content. They
implement the prime-quotient argument directly from the published definitions
of `center`, `pointSeminorm` and `ExtendsNorm`, and Mathlib's quotient and finite-type
algebra APIs. They are not additional statements attributed to the literature.
The source correspondence and complete hypotheses of the eventual target are
documented in `AnalytificationCenterStatement.md`.

## Implemented proof

For a prime ideal `p` of `A`, let `n : MulRingSeminorm (A ⧸ p)` restrict to
the norm of `K` and satisfy `∀ a, n a = 0 → a = 0`. Pull it back along the
quotient map to a multiplicative seminorm `ν` on `A`. Compatibility of the
quotient algebra map with scalars proves `ExtendsNorm K ν`. Faithfulness of `n` and
`Ideal.Quotient.eq_zero_iff_mem` give
`ν a = 0 ↔ a ∈ p`.

Under the seminorm range property, choose `x : Space K P` whose seminorm is `ν`.
The center ideal of `x` is, by definition, the zero set of that seminorm.
Extensionality of ideals and prime-spectrum points therefore gives
`center K P x = p`.

The final lemma deduces the hypothesis about prime quotients from the existence
of faithful extending seminorms on all finite-type `K`-domains. Its norm-extension
premise is exactly
`∀ (D : Type v) [CommRing D] [IsDomain D] [Algebra K D] [Algebra.FiniteType K D],
∃ n : MulRingSeminorm D, ExtendsNorm K n ∧ ∀ a : D, n a = 0 → a = 0`.
Thus it takes the `FiniteTypeDomainNormExtensionStatement` interface
specialized to `K`, without requiring a conversion to `MulRingNorm`. The polynomial
surjection in `P` establishes `Algebra.FiniteType K A`; finite type descends to
`A ⧸ p`, which is a domain because `p` is prime.

## Scope and dependencies

The field `K : Type u` is complete, ultrametric and nontrivially normed, while
`A : Type v` has an independent universe. The ring `A` may have zero divisors,
nilpotents or no prime ideals. The proof makes no domain assumption on `A`.

Only the published definitions and statements in `AnalytificationCenter` and
`AffineAnalytificationSeminormStatement` are imported. The range property and
the norm-extension theorem remain explicit premises here; `AnalytificationCenterProof`
supplies them from `AffineAnalytificationSeminormProof` and
`FiniteTypeDomainNormExtensionProof`. No scheme or rational-fibre clause is asserted
by this helper module.
