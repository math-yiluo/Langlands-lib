# Elementary tools for regular-local factoriality

This module supplies auxiliary lemmas used by `RegularLocalFactorialProof`
to prove factoriality of regular local rings. Its own conclusions are the
elementary ingredients listed below.

The namespace is
`Langlands.CommutativeAlgebra.RegularLocalFactorial`. The ring lives in an
arbitrary universe. The first six lemmas assume Mathlib's
`IsRegularLocalRing`; the last uses an arbitrary Noetherian domain.

- `isRegularLocalRing_quotient_span_singleton`: if `x` lies in the maximal
  ideal but outside its square, `R/(x)` is regular local.
- `spanFinrank_quotient_add_one`: the minimal number of generators of the
  quotient's maximal ideal, plus one, equals the original number. Its result
  installs the preceding quotient-regularity theorem as a local instance
  so that the quotient's maximal ideal is defined, without adding a premise.
- `prime_of_mem_maximalIdeal_notMem_sq`: every such `x` is a prime element.
- `exists_prime_parameter`: when the maximal ideal needs a nonzero number
  of generators, such a prime parameter exists.
- `isPrincipalIdealRing_of_spanFinrank_le_one`: a regular local ring with
  embedding dimension at most one is a principal ideal ring.
- `uniqueFactorizationMonoid_of_ringKrullDim_le_one`: regular local rings
  of Krull dimension at most one have unique factorization.
- `uniqueFactorizationMonoid_of_height_one_principal`: a Noetherian domain
  is a UFD if every prime ideal of height one is principal.

The quotient regularity proof extracts the cotangent-space and dimension
argument already implemented in the published `RegularLocalDomainProof`.
Its generator bound is
`RegularLocalDomain.spanFinrank_maximalIdeal_quotient_add_one_le`. Krull's
principal ideal theorem gives the reverse dimension bound. Cancelling one
shows regularity; applying the regularity equalities again gives the exact
generator drop. The published theorem `regularLocalDomain` makes the
quotient a domain, hence `(x)` is prime and `x` is prime.

Parameter existence follows from Nakayama: if the maximal ideal were
contained in its square, it would be zero, contradicting the hypothesis
on its number of generators. In embedding dimension zero every proper
ideal lies in the zero maximal ideal, so the ring is principal. In
embedding dimension one Mathlib's cotangent-space criterion gives a DVR.
These facts prove the stated factoriality cases.

For the height-one criterion, take a nonzero element in an arbitrary
nonzero prime ideal and a minimal prime over its principal ideal.
Krull's principal ideal theorem bounds its height by one, and the domain
condition and the chosen nonzero element exclude height zero. A principal
generator is then a prime element in the original ideal. Mathlib's
Kaplansky criterion concludes unique factorization.

This arrangement is an internal derived argument using the published
domain proof and Mathlib lemmas. The unrestricted source result is Stacks Project Lemma 15.123.2,
[Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0), retained in registered source
`stacks-regular-local-ufd-2026-10-29`. The present file proves only the
listed elementary ingredients. In particular it does not establish the
principal height-one-ideal hypothesis, regularity of arbitrary
localizations of regular local rings, or `Pic(R_f)=0`.
