# Polynomials with vanishing partial derivatives

Author: Worker 1389 designed and implemented this module and wrote this note, as
part of task `90ffbd89-a3dd-4baa-84ba-332896bbbd17` (split unipotence from the
absence of zero Lie weights). No other worker's draft was reused. Provenance: internal.
These are elementary facts about multivariate polynomials over a field, used in
`Langlands.Algebra.GradedHopf.Primitive` for the characteristic-`p` step of Lemma A. They
rely on Mathlib's `MvPolynomial.pderiv`, `MvPolynomial.expand`, `coeff_pderiv`,
`map_frobenius_expand` and `coeff_expand_smul`.

Throughout, `k` is a field and `σ` a type of variables. Coefficients are written
`F.coeff m`.

## Vanishing partial derivatives

- `cast_eq_zero_of_pderiv_eq_zero`: if `pderiv i F = 0` for all `i`, then for every
  exponent vector `m` in the support of `F` and every `i`, the natural number `m i` is
  zero in `k`. Proof: by Mathlib's `coeff_pderiv`, the coefficient of
  `m - single i 1` in `pderiv i F` is `F.coeff m * m i` (as an element of `k`). It
  vanishes, and `F.coeff m ≠ 0`.
- `eq_C_of_pderiv_eq_zero`: in characteristic zero (`CharZero k`) such an `F` is the
  constant `C (F.coeff 0)`.
- `exists_expand_of_pderiv_eq_zero p`: in characteristic `p` (`CharP k p`, `p` prime)
  such an `F` is `expand p H` for some polynomial `H`, i.e. a polynomial in the `p`-th
  powers of the variables. `H` has the coefficient `F.coeff m` at `m / p` (coordinatewise
  division, exact because `p` divides every `m i`).

## p-independent decompositions

Let `k` have characteristic `p` prime.

- `PIndependent p b`, for `b : Fin r → k`, means
  `∀ c : Fin r → k, ∑ j, b j * c j ^ p = 0 → ∀ j, c j = 0`. This is linear independence
  over the subfield of `p`-th powers.
- `exists_pIndependent_decomposition p H`: every polynomial `H` can be written as
  `H = ∑ j, b j • (G j).map (frobenius k p)`, with `p`-independent `b` and
  `(G j).support ⊆ H.support`. Here `(G j).map (frobenius k p)` raises every coefficient
  to the `p`-th power. Proof: the coefficients of `H` span a finite-dimensional vector
  space `V` over the subfield `K = (frobenius k p).fieldRange` of `p`-th powers. Let `b`
  be a basis of `V` (Mathlib's `Module.finBasis`). Expand each coefficient in this basis.
  Each basis coordinate lies in `K`, so it is a `p`-th power `γ ^ p`. `G j` collects the
  roots `γ`. `p`-independence of `b` is linear independence of the basis.
- `eq_zero_of_sum_smul_pow_eq_zero p hb`: if `b` is `p`-independent and
  `∑ j, b j • h j ^ p = 0` in a polynomial ring `MvPolynomial τ k`, then every `h j` is
  zero. Proof: `h ^ p = (expand p h).map (frobenius k p)`, so the coefficient of
  `p • m` in the sum is `∑ j, b j * (h j).coeff m ^ p`, which therefore vanishes.
