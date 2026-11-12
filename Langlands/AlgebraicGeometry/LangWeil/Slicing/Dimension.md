# Dimension of hypersurface sections of irreducible affine schemes

Author: Worker 5132.

This helper module holds the dimension theory used in the hyperplane-slicing step
`FamilyLangWeilSlicingStatement`. Let `T` be a commutative ring whose nilradical is prime, so
that `Spec T` is irreducible. Killing an ideal not contained in the nilradical lowers the Krull
dimension by at least one. When `T` is of finite type over a field, killing one non-unit lowers
it by at most one. So a hyperplane section that does not contain the whole variety has dimension
exactly one less.

## Provenance

Provenance: internal. These are standard consequences of Krull's principal ideal theorem and of
the dimension formula `ht q + dim (T ⧸ q) = dim T` for affine domains. The Lean proofs use
Mathlib's
`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes` and the Library's
`Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType`.

## Declarations

- `ringKrullDim_quotient_nilradical`: `dim (T ⧸ nil T) = dim T`. Proof: the quotient map
  induces a homeomorphism of prime spectra (`PrimeSpectrum.isHomeomorph_comap`).
- `ringKrullDim_quotient_succ_le_of_not_le_nilradical hT hI`: if `nil T` is prime and
  `I ⊄ nil T`, then `dim (T ⧸ I) + 1 ≤ dim T`. Proof: every chain of primes containing `I` can
  be extended below by the prime `nil T`. The case `I = ⊤` is trivial.
- `ringKrullDim_le_quotient_span_singleton_add_one k hT hne`: if `T` is of finite type over a
  field `k`, `nil T` is prime and `(h) ≠ T`, then `dim T ≤ dim (T ⧸ (h)) + 1`. Proof: choose a
  maximal ideal containing `h` and a minimal prime `q` of `(h̄)` in the affine domain
  `T ⧸ nil T` below it. Krull's principal ideal theorem gives `ht q ≤ 1`. The dimension formula
  gives `dim (T ⧸ nil T) = ht q + dim ((T ⧸ nil T) ⧸ q)`, and the last ring is a quotient of
  `T ⧸ (h)`.
- `hasPureRingDimension_of_isPrime_nilradical hA he`: a ring with prime nilradical and Krull
  dimension `e` has pure dimension `e` (the Library's `HasPureRingDimension`). Proof: its only
  minimal prime is the nilradical.
- `ringKrullDim_quotient_span_singleton_eq k hT hh hne he`: if `T` is of finite type over `k`,
  `nil T` is prime, `dim T = e + 1`, `h ∉ nil T` and `(h) ≠ T`, then `dim (T ⧸ (h)) = e`. Proof:
  combine the two inequalities above.
