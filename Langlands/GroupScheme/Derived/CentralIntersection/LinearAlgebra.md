# Linear algebra for the central intersection finiteness proof

Author: Worker 1408.

This internal helper module collects elementary algebra used by the
scheme-theoretic argument in
`Langlands.GroupScheme.Derived.CentralIntersection.AlgClosed`. It is derived
content: the statements are standard facts about ring endomorphisms, nilpotent
matrices, eigenvalues and polynomials, proved directly in Lean. Nothing here
involves group schemes. Namespace: `Langlands.GroupScheme.CentralIntersection`.

## Locally unipotent elements of a ring endomorphism

Let `A` be a commutative ring and `φ : A →+* A` a ring endomorphism.

- `diff φ` is the additive map `f ↦ φ f - f`. `diff_mul` is the twisted
  Leibniz rule `diff φ (f g) = diff φ f · φ g + f · diff φ g`. `diff_comp`
  says that `diff φ` commutes with `φ`.
- `iterate_diff_mul_eq_zero`: if `(diff φ)^[a] f = 0` and `(diff φ)^[b] g = 0`,
  then `(diff φ)^[a + b] (f g) = 0`. The proof is by induction on `a + b` with
  the twisted Leibniz rule.
- `locallyUnipotent φ` is the subring of all `f` with `(diff φ)^[k] f = 0` for
  some `k`. Closure under products is the previous lemma. Fixed elements of `φ`
  belong to it (`mem_locallyUnipotent_of_fixed`).
- For square matrices, `iterate_diff_matrix` computes the iterated entrywise
  difference operator entry by entry. If `φ` fixes a matrix `B` and
  `φ.mapMatrix M = M * B`, then the `k`-th iterate sends `M` to
  `M * (B - 1)^k` (`iterate_diff_matrix_eq_mul`). The version with left
  multiplication `φ.mapMatrix M = B * M` gives `(B - 1)^k * M`
  (`iterate_diff_matrix_eq_mul_left`).
- Hence, if `B - 1` is nilpotent, every entry of `M` is locally unipotent
  (`mem_locallyUnipotent_of_mapMatrix_eq_mul` and its `_left` version).
- Conversely, `isNilpotent_sub_one_of_mapMatrix_eq_mul`: if `M` is invertible,
  `φ` fixes `B`, `φ.mapMatrix M = M * B` and every entry of `M` is locally
  unipotent, then `B - 1` is nilpotent. Take `K` to be the sum of the exponents
  of all entries. Then the `K`-th iterate kills `M`, so `M (B - 1)^K = 0`, and
  invertibility of `M` gives `(B - 1)^K = 0`.

## Common kernel vectors

Let `V` be a finite-dimensional vector space over a field `K`.

- `exists_mem_ne_zero_apply_eq_zero`: a nilpotent endomorphism `a` preserving a
  subspace `W` with a nonzero vector `w` kills a nonzero vector of `W`, namely
  `a^j w` for the least `j` with `a^(j+1) w = 0`.
- `exists_ne_zero_forall_eq_zero`: if `V ≠ 0` and `s` is a set of pairwise
  commuting nilpotent endomorphisms, then some nonzero `v` satisfies `a v = 0`
  for all `a ∈ s`. Take a minimal nonzero subspace `W` invariant under `s`;
  it exists by well-foundedness of submodules of `V`. For `a ∈ s`, the subspace
  `W ∩ ker a` is nonzero by the previous lemma and `s`-invariant by
  commutativity, so it equals `W`. Thus every nonzero vector of `W` works.

## Block projectors

Let `K` be algebraically closed and `A₀` a square matrix over `K` indexed by a
finite type `n`.

- `multiset_prod_eq_pow_count`: a multiset whose elements are all `c` or `1` has
  product `c` raised to the number of occurrences of `c`.
- `exists_blockProjector`: if `c` is a root of the characteristic polynomial of
  `A₀`, there is a polynomial `P` such that `π = P(A₀)` is idempotent and
  `det (A₀ π + (1 - π)) = c^a` for some `1 ≤ a ≤ card n`. Write the
  characteristic polynomial as `(X - c)^m r` with `r(c) ≠ 0`, choose a Bézout
  relation `u (X - c)^m + w r = 1`, and set `P = w r`. Idempotency of `π`
  follows from Cayley–Hamilton. The matrix `A₀ π + (1 - π)` is `G(A₀)` for
  `G = X P + 1 - P`. By the spectral mapping theorem
  (`spectrum.map_polynomial_aeval_of_nonempty`), its eigenvalues are the values
  of `G` at eigenvalues of `A₀`. These are `c` at `c` (since `P(c) = 1`) and `1`
  at every other eigenvalue (since `r` vanishes there). The determinant is the
  product of the roots of the characteristic polynomial
  (`Matrix.det_eq_prod_roots_charpoly`). So it is `c^a`, where `a` is the
  multiplicity of `c` among these roots: positive because `c` occurs, and at
  most `card n`.

## Idempotent splitting off the eigenvalue `1`

- `exists_unipotent_splitting`: a nonzero polynomial `Q` over a field with root
  `1` factors as `(X - 1)^e R` with `u (X - 1)^e + w R = 1` and
  `(w R)(1) = 1`.
- `splitting_aeval`: in any `K`-algebra, if `Q(a) = 0` for such a factorization,
  then `E = (w R)(a)` is idempotent and `(a - 1)^e E = 0`.
- `aeval_pow_sub_one_eq_zero`: over an algebraically closed field, a matrix
  `X'` all of whose characteristic-polynomial roots satisfy `μ^N = 1` is
  annihilated by `(X^N - 1)^(card n + 1)`. The characteristic polynomial splits
  into linear factors `X - μ`, each dividing `X^N - 1`, and it has at most
  `card n` roots. So it divides that power, and Cayley–Hamilton applies.
