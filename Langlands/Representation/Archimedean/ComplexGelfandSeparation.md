# Gelfand's central elements separate shifted diagonals up to permutation

Lean module: `Langlands.Representation.Archimedean.ComplexGelfandSeparation`, namespace
`Langlands.Archimedean.GelfandSeparation`.

This module holds no statement definition. It proves a lemma of pure algebra about the
Library's Gelfand polynomials, used by `ComplexJacquetCasselmanOsborneProof`. All content is
internal.

## Setting

`ComplexJacquetFinite.gelPoly n k a` (Library) are the polynomials in `X_0, …, X_{n-1}` with
`g_0(a) = 1` and `g_{k+1}(a) = (X_a + a) g_k(a) - ∑_{c < a} g_k(c)` (`a` is the 0-based index).
For a Jacquet functional they compute the action of Gelfand's central element `tr E^k` modulo
`𝔫V` (`ComplexJacquetFinite.diag_pow`).

- `gv x k a` is the value `g_k(a)(x)` for `x : Fin n → ℂ`; `gv_zero`, `gv_succ` restate the
  recursion.
- `ll x a = x_a + a`.

## Main result

`exists_perm_of_gel_eq`: if `∑_a g_k(a)(x) = ∑_a g_k(a)(y)` for every `k`, then there is a
permutation `σ` of `Fin n` with `x_a + a = y_{σ a} + σ a` for every `a`.

## Proof

1. **Generating series.** `ser x a = ∑_k g_k(a)(x) t^k` (a formal power series). The recursion
   is equivalent to `ser_mul`: `G_a (1 - l_a t) = 1 - t ∑_{c < a} G_c` (compare coefficients).
2. **Product identity.** `prod_identity_aux` (induction on `m`, adding the index `m` to the set
   `{c < m}`) and `prod_identity`:
   `(1 - t ∑_a G_a) ∏_a (1 - l_a t) = ∏_a (1 - (l_a + 1) t)`.
   In the inductive step, with `S = ∑_{c<a} G_c`:
   `(1 - t(G_a + S))(1 - l_a t) = (1 - tS)(1 - l_a t) - t(1 - tS) = (1 - tS)(1 - (l_a + 1)t)`.
3. **Polynomials.** `pol A = ∏_{c ∈ A} (1 - c t)` for a multiset `A` of complex numbers;
   `pol_add`, `coe_pol` (its image in power series). `roots_pol`: the roots of `pol A` are the
   inverses of the nonzero elements of `A`. `eq_of_pol_eq`: `pol A = pol B` and
   `card A = card B` imply `A = B` (the nonzero elements agree by `roots_pol`, the numbers of
   zeros by the cardinalities).
4. **Comparison.** If the Gelfand sums agree, the series `∑_a G_a` for `x` and `y` agree, so with
   `L_x = {l_a(x)}`, `L_y = {l_a(y)}` the product identity gives
   `pol(L_x + 1) pol(L_y) = pol(L_y + 1) pol(L_x)` (first in power series, then in polynomials
   by injectivity of the coercion), hence `(L_x + 1) + L_y = (L_y + 1) + L_x` as multisets.
5. **Shift argument.** `eq_of_shift`: `(A + 1) + B = (B + 1) + A` implies `A = B`. The difference
   of multiplicities `f(z) = count_A(z) - count_B(z)` satisfies `f(z - 1) = f(z)`; if
   `f(z) ≠ 0`, then `z, z - 1, z - 2, …` all lie in the finite support of `A + B`, which is
   impossible.
6. **Permutation.** `exists_perm_of_map_eq`: equal multisets of values give a permutation, from
   equivalences of the fibres (`Fintype.equivOfCardEq`, `Equiv.ofFiberEquiv`).

## Provenance

Internal. The generating function `1 - t ∑_a G_a(t) = ∏_a (1 - (l_a + 1) t)/(1 - l_a t)` is the
classical generating function of the eigenvalues of Gelfand's central elements of `U(𝔤𝔩_n)` on
highest-weight vectors (Perelomov–Popov); here it is derived directly from the Library's
recursion and no literature statement is used.
