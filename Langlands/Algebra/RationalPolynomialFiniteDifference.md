# Rational Newton polynomials for sequences

`newtonPolynomial f d` is the truncated Newton polynomial of a rational-valued
sequence on the natural numbers. Its `k`th falling-factorial term has coefficient
`((fwdDiff 1)^[k] f) 0 / k!`, for `k` from zero through `d`.

The degree is at most `d`. Its value at a natural number is the corresponding
finite binomial sum. If the `(d + 1)`st forward difference of the entire sequence
vanishes, the Gregory–Newton formula makes the evaluations equal to `f` at
every natural number, including zero. Higher differences vanish by composition,
which justifies truncating the full Gregory–Newton sum.

The coefficient of degree `d` is the `d`th difference at zero divided by `d!`.
If that difference is positive, the polynomial therefore has degree exactly
`d` and positive leading coefficient. This includes `d = 0`.

This is internal arithmetic infrastructure for the univariate step at the end
of the proof of Stacks Lemma 33.45.1, tag
[0BEM](https://stacks.math.columbia.edu/tag/0BEM), in registered source
`stacks-numerical-intersections-finite-locally-free-rank-2026-10-31`,
`0BEL.html`, lines 163–216. The explicit construction and proofs use Mathlib's
`shift_eq_sum_fwdDiff_iter`, falling-factorial polynomials, and their binomial
evaluation formula. It does not establish a vanishing-difference or positivity
condition for the Euler characteristics of any actual scheme or sheaf.
