# Linear algebra for the quotient by the centre

Author: Worker 1499.

This internal helper module of the proof of
`Langlands.GroupScheme.CenterQuotientReductiveStatement` collects elementary
matrix facts. It is derived content: the statements are standard linear algebra
chosen for the elementary route of the proof (no Jordan decomposition inside the
group), not items of the cited literature. Everything is in the namespace
`Langlands.GroupScheme.CenterQuotient`.

## Rings

For an arbitrary ring `A`:

- `isIdempotentElem_mul_add_one_sub`: if `P` and `P'` are commuting
  idempotents, then `P P' + (1 - P)` is idempotent. The proof multiplies out the
  four products using `P (1 - P) = 0`.
- `isNilpotent_mul_sub_one`: if `a` and `b` commute and `a - 1`, `b - 1` are
  nilpotent, then `a b - 1` is nilpotent, from
  `a b - 1 = (a - 1)(b - 1) + (a - 1) + (b - 1)` and nilpotence of sums and
  products of commuting nilpotents.
- `isNilpotent_inv_sub_one`: for a unit `u` with `u - 1` nilpotent,
  `u⁻¹ - 1 = -(u - 1) u⁻¹` is nilpotent.
- `isNilpotent_mul_inv_sub_one`: for a unit `γ` commuting with `γ'` and
  `γ' - γ` nilpotent, `γ' γ⁻¹ - 1 = (γ' - γ) γ⁻¹` is nilpotent.

## Polynomial evaluation in an algebra

For a commutative semiring `R` and an `R`-algebra `A` that is a ring:

- `commute_aeval_right`: if `a` commutes with `b`, then `a` commutes with every
  polynomial `Q(b)`, by induction on `Q` (sums and monomials).
- `commute_aeval`: if `a` and `b` commute, then `P(a)` and `Q(b)` commute for
  all polynomials `P`, `Q` (two applications of the previous lemma).
- `aeval_units_conj`: for a unit `u`, `P(u a u⁻¹) = u P(a) u⁻¹`, by induction on
  `P` using `(u a u⁻¹)^k = u a^k u⁻¹` and centrality of the scalars.

## Matrices over a field

Let `K` be a field and `n` a finite type with decidable equality.

- `eq_one_of_isIdempotentElem_of_det_eq_one`: an idempotent matrix of
  determinant `1` is invertible, hence the identity.
- `isIdempotentElem_det`: the determinant of an idempotent matrix is
  idempotent, by multiplicativity of `det`.
- `pow_card_eq_zero_of_isNilpotent`: a nilpotent matrix `N` satisfies
  `N ^ card n = 0`; its characteristic polynomial is `X ^ card n` (Mathlib's
  `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent`), and Cayley–Hamilton
  applies.
- `eq_one_of_mem_roots_of_isNilpotent_sub_one`: if `A - 1` is nilpotent, every
  root of the characteristic polynomial of `A` is `1`: an eigenvector of `A`
  with eigenvalue `c` is an eigenvector of the nilpotent `A - 1` with eigenvalue
  `c - 1`, which must be `0`.
- `exists_blockPolynomial`: for a root `c` of the characteristic polynomial `χ`
  of `γ`, there is a polynomial `P` with `P(c) = 1`, `P(μ) = 0` at every other
  root `μ` of `χ`, and `P(γ)` idempotent. Write `χ = (X - c)^m r` with
  `X - c ∤ r`; Bézout gives `u (X - c)^m + w r = 1`, and `P = w r` works:
  evaluating the Bézout identity at `c` gives `P(c) = 1`, `r` vanishes at the
  other roots, and `P(γ) (1 - P(γ)) = w u χ(γ) = 0` by Cayley–Hamilton. The
  argument follows the Library proof of
  `CentralIntersection.exists_blockProjector`.

Over an algebraically closed field `K`:

- `exists_isRoot_ne_zero_of_not_isNilpotent`: a matrix that is not nilpotent
  has a nonzero root of its characteristic polynomial. Otherwise the
  characteristic polynomial splits as `X ^ m` and Cayley–Hamilton makes the
  matrix nilpotent.
- `isNilpotent_sub_of_forall_blockPolynomial` (**nested blocks force a
  nilpotent difference**): let `γ` and `γ'` commute, and suppose that for every
  root `c` of the characteristic polynomial of `γ` and every different root `c'`
  of that of `γ'` there is a polynomial `P` with `P(c) = 1`, `P(c') = 0` and
  `P(γ) P(γ') = P(γ)`. Then `γ' - γ` is nilpotent.

  Proof by contradiction, working with the linear endomorphisms `f`, `f'` and
  `N = f' - f` of `K^n`. A nonzero eigenvalue `d` of `N` exists. Since `f`
  commutes with `N`, it preserves the `d`-eigenspace of `N`, and its
  restriction has an eigenvector `v` with some eigenvalue `c` (algebraic
  closure). Then `f' v = (c + d) v`, so `c` is a root for `γ`, `c + d ≠ c` is a
  root for `γ'`, and the hypothesis gives `P`. Evaluating
  `P(γ) P(γ') = P(γ)` at `v` gives `P(c) P(c + d) v = P(c) v`, that is
  `0 = v`, a contradiction.

In the proof of the target, `γ` is the matrix of a rational point `h` of the
preimage of a normal commutative unipotent subgroup, `γ'` that of a conjugate
`g h g⁻¹`, and the hypothesis on block polynomials is supplied by a
connectedness argument; `isNilpotent_mul_inv_sub_one` then shows that the
commutator `g h g⁻¹ h⁻¹` acts unipotently.
