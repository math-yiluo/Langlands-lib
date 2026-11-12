# Finite counting from two auxiliary polynomials

Author: Worker 96.

`StepanovCountingStatement` states the counting and integer parameter step
of Schmidt's method independently of any plane curve. This module states
the proposition and does not prove it.

Let `F` be a finite field with `q` elements, supplied with an enumeration,
and let `r : F → ℕ` be any function. Suppose `m ≥ n ≥ 2` and
`q > 9(m+1)²(n+1)²`. The auxiliary-polynomial hypothesis says that, for
every positive integer `M` with

`M²(n²+1)+(M+m)n² < q` and `Mn ≤ q`,

there are a finite subset `s ⊆ F` and two polynomials `h₁,h₂ ∈ F[X]`
such that:

- `q < |s|+2mn` and `r(x) ≤ n` for every `x ∈ F`;
- writing `E=2m(n−1)+1`, their degrees are less than `q(M+E)` and
  `q((n−1)M+E)`, respectively;
- at `x ∈ s`, their root multiplicities are at least `Mr(x)` and
  `M(n−r(x))`, respectively.

The conclusion is

`|Σ_x r(x) − q| < 2mn² sqrt(q)`.

The statement contains no polynomial in two variables, absolute
irreducibility condition, discriminant, function field, or asserted
auxiliary construction. Its explicitly quantified polynomial hypothesis
is a finite algebraic input. Applying it to a curve still requires
constructing these polynomials without assuming a point-count theorem.
Nonzero hypotheses on `h₁,h₂` are unnecessary for this counting
implication: the standard sum of root multiplicities is bounded by
natural degree even for the zero polynomial, whose root multiplicities
and natural degree are zero.

Provenance: derived abstraction of Wolfgang M. Schmidt,
*Zur Methode von Stepanov*, Acta Arithmetica 24 (1973), Section 7,
printed pp.359–360, especially equation (40) and its following parameter
choice, together with Section 9, printed p.367. Registered source:
`schmidt-1973-zur-methode-von-stepanov`, SHA256
`a46364b77f152a1656fa6d60181492cfb868803eae767a2145be38fd20bbdd4d`.
PDF pages 7–8 and 11 contain these passages.

Summing root multiplicities bounds `M Σ_s r(x)` and
`M Σ_s(n−r(x))` by the two polynomial degrees. The omitted fibres
contribute at most `2mn²`. One then chooses an admissible integer `M`
and compares the resulting error with the displayed strict square-root
bound. This is the numerical step after Schmidt's Hilfssatz 6; it does
not replace the substantial norm-polynomial existence proof.
