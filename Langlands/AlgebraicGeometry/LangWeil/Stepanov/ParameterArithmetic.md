# Parameter arithmetic for the Stepanov method

Author: Worker 78. Worker 5406 fixed the Lean interface for the Stepanov
norm-polynomial construction (Task 5406). The module imports only Mathlib.

## Provenance

Wolfgang M. Schmidt, *Zur Methode von Stepanov*, Acta Arithmetica 24 (1973),
§§5–6 (registered source `schmidt-1973-zur-methode-von-stepanov`), builds
auxiliary polynomials. To do so it chooses integer parameters and needs some
elementary inequalities between them. The exact form of the parameters and
inequalities here is the one Worker 5406's Lean adaptation of that construction
uses, not a verbatim transcription of Schmidt's formulas.

The parameters are:

- `n`, the `Y`-degree of the curve;
- `m ≥ n`, a bound for its `X`-degree;
- `M ≥ 1`, the multiplicity parameter;
- `q`, the field size;
- `d = ⌊q/n⌋ − m n`, the `X`-degree bound of the unknown coefficients. This is
  Schmidt's bound `q/n − m n` in Hilfssatz 3;
- `N₁ = ⌊(M + m)/n⌋` and `N₂ = ⌊(n − 1)(M + m)/n⌋`.

This module only proves the inequalities. It makes no claim about how they are
used.

## Statement

`Langlands.AlgebraicGeometry.LangWeil.Stepanov.stepanovParameterArithmetic`
assumes `2 ≤ n ≤ m`, `0 < M` and

`M² (n² + 1) + (M + m) n² < q`.

With `d, N₁, N₂` as above (natural-number floor division and truncated
subtraction), it proves five inequalities:

1. `n d + m (n − 1)² < q`. This is the hypothesis of Frobenius independence
   (Hilfssatz 3, module `Stepanov/FrobeniusIndependence`) for coefficient
   degree `d`.
2. `∑_{l < M} (n (d + l(2m − 1) + N₁ + 1) + m((n − 1)(2l + 2) + 1 − n))
   < n² (N₁ + 1)(d + 1)`. This is the first dimension count.
3. `(n − 1) ∑_{l < M} (n (d + l(2m − 1) + N₂ + m + 1) + m((n − 1)(2l + 2) + 1 − n))
   < n² (N₂ + 1)(d + 1)`. This is the second dimension count.
4. `m (n − 1)(q + 1) + n (d + q N₁) < q (M + 2m(n − 1) + 1)`.
5. `m (n − 1)(q + 1) + n (d + q N₂) < q ((n − 1) M + 2m(n − 1) + 1)`.

The Lean statement writes these with the exact expressions above, including the
`let`-bound `d, N₁, N₂`.

## Proof

1. **Floor-division facts.** The hypothesis gives `m n² < q`, so
   `m n ≤ ⌊q/n⌋`. From `n ⌊q/n⌋ + (q mod n) = q` and `q mod n < n` we get

   `n d + m n² ≤ q < n d + n + m n²`.

   `Nat.mul_div_le` and `Nat.lt_mul_div_succ` give

   `n N₁ ≤ M + m < n (N₁ + 1)` and `n N₂ ≤ (n − 1)(M + m) < n (N₂ + 1)`.

   After this, `d, N₁, N₂` are treated as opaque numbers satisfying these
   bounds (`clear_value`).
2. **Substitution.** Put `n = a + 2`, `m = c + 1` and `M = s + 1`. This removes
   every truncated subtraction:
   - `n − 1 = a + 1` and `2m − 1 = 2c + 1`;
   - `(n − 1)(2l + 2) + 1 − n = (n − 1)(2l + 1)`.
3. **Closed form of the sums.** Each summand is `α + β l`, where
   `β = n(2m − 1) + 2m(n − 1)` and
   - `α = n(d + N + 1) + m(n − 1)` for the first sum,
   - `α = n(d + N + m + 1) + m(n − 1)` for the second.

   `ParamArith.two_mul_sum_affine` proves

   `2 ∑_{l ≤ s} (α + β l) = 2α(s + 1) + β(s + 1)s`

   from `Finset.sum_range_id_mul_two`.
4. **Key lower bound.** Write `A = n(d + 1)`. The hypothesis and
   `q < n d + n + m n²` give

   `X + 2 ≤ A`, where `X = M²(n² + 1) + M n²`.
5. **Counts (2) and (3).** Let `B = n(N + 1)`.
   - For (2), `B ≥ M + m + 1`. Multiplying by `A` gives
     `AB − M A ≥ (m + 1) A ≥ (m + 1)(X + 2)`.
   - For (3), `B ≥ (n − 1)(M + m) + 1`. This gives
     `AB − (n − 1) M A ≥ ((n − 1) m + 1)(X + 2)`.

   We also use `n N ≤` the corresponding numerator. Each count then reduces to
   an inequality between polynomials in `a, c, s`:
   - (2): `2M(M + m) + 2M m(n − 1) + β M s < 2(m + 1)(X + 2)`;
   - (3): `2(n − 1)² M(M + m) + 2(n − 1) M m(2n − 1) + (n − 1) β M s
     < 2((n − 1) m + 1)(X + 2)`.

   In both cases, right side − left side is an explicit polynomial in `a, c, s`
   with nonnegative coefficients and a positive constant term (38, resp. 34).
   It is written out in the proof (`Q1`, `Q2`), checked by `ring`, and shown to
   be positive by `positivity`. `linarith` then combines the product facts.
6. **Bounds (1), (4) and (5).** These follow by `linarith` from:
   - `n d + m n² ≤ q`;
   - `q · n N ≤ q · (numerator)`;
   - nonnegativity of a few monomials.

   The slack is at least:
   - (1): `m(2n − 1)`;
   - (4): `q m (n − 2) + m(n² − n + 1)`;
   - (5): `m(n² − n + 1)`.

## Check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`:

- 0 errors, 0 warnings (diagnostic `4774b543`);
- axioms are only `propext`, `Classical.choice` and `Quot.sound` (diagnostic
  `47d7f3ec`).
