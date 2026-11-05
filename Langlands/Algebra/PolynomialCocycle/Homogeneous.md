# Homogeneous symmetric polynomial 2-cocycles

Module: `Langlands.Algebra.PolynomialCocycle.Homogeneous`.

This module is the coefficient-level core of the polynomial cocycle lemma
`Langlands.Algebra.PolynomialCocycle.exists_coboundary` (module
`Langlands.Algebra.PolynomialCocycle.Coboundary`). It is internal to the proof of
`Langlands.GroupScheme.RelativeRoot.SplitUnipotentStableVectorSubgroupStatement`, where
the lemma shows that a commutative split unipotent group of exponent `p` is a vector
group. The content is derived for this proof. It is a special case of the classical
description of symmetric polynomial 2-cocycles (Lazard's lemma): a homogeneous one of
degree `n` is a multiple of `((x + y)^n - x^n - y^n) / d`, where `d = p` if `n` is a
power of a prime `p` and `d = 1` otherwise. The module does not prove that description.
It proves only the case needed here: once the torsion condition holds, the homogeneous
cocycle is a multiple of the binomial coboundary.

Throughout, `k` is a field. A family `d : ℕ → k` encodes the homogeneous polynomial
`c(x, y) = ∑_{i ≤ n} d i · x^i y^(n-i)` of degree `n`.

## Declarations

- `powerSum k p j`: the power sum `∑_{i < p} i^j`, computed in `k`.
- `IsHomCocycle n d`: the coefficient conditions on `d` for `c` above to be a symmetric
  2-cocycle with `c(0, y) = 0`. The fields are:
  - `zero`: `d 0 = 0`;
  - `top`: `d n = 0`;
  - `symm`: `d i = d (n - i)` for `i ≤ n`;
  - `coc`: `d (a + b) · C(a + b, a) = d a · C(n - a, b)` for `0 < a`, `0 < b` and
    `a + b < n`. Here `C(m, r)` is the binomial coefficient cast to `k`.

  `coc` compares the coefficients of `x^a y^b z^(n-a-b)`, all three exponents positive, on
  the two sides of `c(x, y) + c(x + y, z) = c(y, z) + c(x, y + z)`. The structure is only
  the list of conditions; the module never derives them from a polynomial identity.
- `IsHomCocycle.mul_eq`: for `0 < j < n`, `j · d j = d 1 · C(n - 1, j - 1)`. This is
  `coc` with `a = 1`.
- `IsHomCocycle.cast_mul_choose`: for `0 < j` and `0 < n`,
  `j · C(n, j) = n · C(n - 1, j - 1)` in `k`.
- `IsHomCocycle.exists_eq_charZero` (with `[CharZero k]`): if `IsHomCocycle n d`, then
  there is `g : k` with `d i = g · C(n, i)` for all `0 < i < n`.
- `cast_choose_mul_mul`, `cast_choose_mul_of_not_dvd`, `cast_choose_mul_sub_one`: three
  cases of Lucas' theorem in a field of characteristic `p` (`p` prime):
  `C(p A, p B) = C(A, B)`; `C(p A, j) = 0` if `p ∤ j`; and `C(p m - 1, p - 1) = 1`
  if `m ≥ 1`.
- `powerSum_mul`: `powerSum k p (p j) = powerSum k p j`, since `i^p = i` for the image of
  `i` in the prime field.
- `sum_zmod_eq_sum_range`: a sum over `ZMod p` equals the sum over `range p` of the
  casts. It needs only `p` prime and no characteristic hypothesis on `k`.
- `powerSum_eq_zero`: `powerSum k p j = 0` for `j < p - 1`.
- `powerSum_sub_one`: `powerSum k p (p - 1) = -1`.
- `IsHomCocycle.exists_eq_charP` (with `p` prime and `[CharP k p]`): if
  `IsHomCocycle n d` and the torsion condition
  `∑_{j ≤ n} powerSum k p j · d j = 0` holds, then there is `g : k` with
  `d i = g · C(n, i)` for all `0 < i < n`. The torsion condition is the degree-`n` part
  of `∑_{i < p} c(i x, x) = 0`.

## Proof

Characteristic zero: by `mul_eq` and `cast_mul_choose`, `i · d i = i · (d 1 / n) · C(n, i)`
for `0 < i < n`. Cancel `i ≠ 0` and take `g = d 1 / n`.

Characteristic `p`, by strong induction on `n`.

- If `p ∤ n`, take `g = d 1 / n`. The same computation gives `d i = g · C(n, i)` whenever
  `p ∤ i`. If `p ∣ i`, then `p ∤ n - i`. Apply the computation to `n - i` and use `symm`
  and `C(n, i) = C(n, n - i)`.
- If `n = p m` with `m = 0`, there is nothing to prove. Otherwise:
  1. `d 1 = 0`. If `m ≥ 2`, this is `coc` with `a = 1`, `b = p - 1`, because `C(p, 1) = 0`
     and `C(p m - 1, p - 1) = 1`. If `m = 1`, the torsion condition reduces to
     `-d (p - 1) = 0`, since the power sums of exponent `< p - 1` vanish, the one of
     exponent `p - 1` is `-1`, and `d p = 0` by `top`. Then `d 1 = d (p - 1) = 0` by `symm`.
  2. `d j = 0` for `p ∤ j`, from `mul_eq` and `d 1 = 0`.
  3. `i ↦ d (p i)` satisfies `IsHomCocycle m`, using `cast_choose_mul_mul` in `coc`.
  4. Its torsion condition holds. By step 2, only indices divisible by `p` contribute to
     the torsion sum for `d`, and `powerSum_mul` identifies their weights.
  5. Since `m < p m`, induction gives `g` with `d (p i) = g · C(m, i)`. Then
     `d j = g · C(p m, j)` for all `0 < j < p m`: for `j = p i` use `cast_choose_mul_mul`;
     for `p ∤ j` both sides vanish by step 2 and `cast_choose_mul_of_not_dvd`.
