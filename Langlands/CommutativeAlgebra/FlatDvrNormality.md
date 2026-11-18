# Normality criteria for algebras flat over a discrete valuation ring

Worker 6.

Namespace `Langlands.CommutativeAlgebra.FlatDvrNormality`. Ring-level lemmas used by the
stable-normal-model construction. Throughout, `π` plays the role of a uniformizer pulled back to a
ring `B` or `C`; no DVR appears in the statements.

## Integral elements with a power of `π` as denominator

- `mem_span_of_isIntegral_mul`: if `B → L` is injective, `B ⧸ π B` is reduced, `x : L` is integral
  over `B`, and `π x = b` with `b ∈ B`, then `b ∈ π B`. Proof: for a monic `p` with `p(x) = 0`,
  `scaleRoots p π` vanishes at `b`, and modulo `π` it becomes `X ^ deg p`, so `b` is nilpotent in
  `B ⧸ π B`.
- `mem_range_of_pow_mul_of_key`: if `π` is cancellable in `L` and every integral `y` with
  `π y ∈ B` satisfies `π y ∈ π B`, then every integral `x` with `π ^ n x ∈ B` lies in `B`
  (induction on `n`).
- `mem_range_of_isIntegral_of_pow_mul`: combination of the two (criterion E1).

## Local normality (criterion E2)

For a Noetherian local ring `B`:

- `isReduced_of_quotient`: if `π` is a non-zero-divisor in the maximal ideal and `B ⧸ π B` is
  reduced, then `B` is reduced (a nilpotent lies in every power of `π B`; Krull intersection).
- `eq_of_minimalPrimes_le`: if the localization at a prime `Q` is a domain, two minimal primes
  contained in `Q` coincide (both equal the kernel of `B → B_Q`).
- `isDomain_of_quotient`: under the hypotheses of `isReduced_of_quotient`, if every localization
  at a prime not containing `π` is a domain, then `B` is a domain. If `P₁ ≠ P₂` are minimal primes
  and `J` is the intersection of the minimal primes other than `P₁`, some `π ^ n` lies in `P₁ + J`;
  for minimal `n`, the decomposition `π ^ n = a₁ + a₂` has `a₁ a₂ = 0`, which forces
  `a₁, a₂ ∈ π B` and contradicts minimality.
- `isIntegrallyClosed_of_quotient`: a domain with `π ≠ 0`, reduced `B ⧸ π B` and integrally
  closed localizations at primes not containing `π` is integrally closed: an integral element of
  the fraction field has denominator ideal containing a power of `π`, then E1 applies.
- `isDomain_and_isIntegrallyClosed_of_quotient`: packages the local case, including the case
  `π ∉ m`.

## Affine forms

For a commutative ring `C`:

- `isReduced_localization_quotient`: if `C ⧸ π C` is reduced, so is `C_p ⧸ π C_p`.
- `isDomain_and_isIntegrallyClosed_localization`: if `C` is Noetherian, `π` is a
  non-zero-divisor, `C ⧸ π C` is reduced and `C_q` is an integrally closed domain whenever
  `π ∉ q`, then every `C_p` is an integrally closed domain.
- `mem_range_of_isIntegral_of_normal` (criterion E3): if `π` is a non-zero-divisor and every
  `C_m` (`m` maximal) is an integrally closed domain, then `C` is integrally closed in any
  localization `L` of `C` away from `π`.

## Provenance

These are standard consequences of Serre's criteria in the special case of a flat algebra over a
DVR, as used in Conrad's appendix to Prasad–Yu, *On quasi-reductive group schemes*, Remark A.3,
author-preprint p.28 (registered source `prasad-yu-2006-quasi-reductive-author-preprint`). The
proofs here are direct and do not use depth or Serre's conditions.
