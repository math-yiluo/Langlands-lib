# A local coercive scalar L² estimate

`Langlands.Analysis.CoordinateScalarCoerciveLocalL2EstimateStatement d r`
states a local estimate for the actual `CoordinateScalarOperator` on
`EuclideanSpace ℝ (Fin d)` with its basis equal to the canonical orthonormal
basis. All coefficients are continuous on an open set `S`. At a specified
point `x₀ ∈ S`, the actual degree `r` ordered-word symbol satisfies
`c ‖ξ‖^r ≤ ‖p(ξ)‖` for every real frequency, with `c > 0`.

There are a radius `R > 0` and a constant `C > 0`, both chosen before the
function, with `closedBall x₀ R ⊆ S`, such that every actual smooth complex
function whose topological support lies in that ball satisfies

`‖T_r F‖₂ ≤ C (‖D.action F‖₂ + ‖F‖₂)`.

Here `T_r F` is exactly the square root of the sum of squared complex norms
of all actual standard-basis evaluations of `iteratedFDeriv ℝ r F`. Every
ordered word, including repeated directions, retains its actual multiplicity.
The Lean statement uses exponent-two `eLpNorm`, canonical volume and
`ENNReal.ofReal C`. It retains the actual full operator action and all its
lower coefficients. Scoped `ContDiff` infinity means smoothness. All dimensions
and orders, including zero and their intersection, are included. The closed
ball is compact, so a separate compact-support hypothesis is unnecessary.

## Symbol convention

The symbol in the hypothesis is written in the coordinates of a Euclidean
vector `ξ`:

`p(ξ) = ∑ w : Fin r → Fin d, D.coefficient (Fin.last r) w x₀ · ∏ j : Fin r, (ξ (w j) : ℂ)`.

It contains neither `i` nor `2π`, exactly as in
`Langlands.Analysis.ConstantCoefficientEllipticL2EstimateStatement` with the
frozen array `a w = D.coefficient (Fin.last r) w x₀`. Because `D.basis` is the
canonical basis, this is the value of `D.principalSymbol x₀` at the covector
`v ↦ ⟪v, ξ⟫`; that identification is explanatory and is not proved or used by
the Lean statement. The hypothesis is imposed at the single point `x₀` only;
no uniform ellipticity on `S` is assumed.

The import of `Langlands.Analysis.ConstantCoefficientEllipticL2EstimateStatement`
supplies the Euclidean, `eLpNorm` and Haar-volume infrastructure and the frozen
constant-coefficient estimate used by the intended proof; the statement does
not mention that proposition.

## Derived provenance and intended proof

This internal derived statement is the result of freezing the continuous
principal coefficients, bounding every lower coefficient on one ball, and
absorbing the lower ordered tensor terms by scale-explicit global L²
interpolation. A small scale is chosen using only the finitely many lower
coefficient bounds and the principal ellipticity constant. Smooth compact
support makes every derivative tensor norm finite, which is needed when
subtracting an absorbed term in an extended-norm proof. Order zero has an
empty lower sum. No separate literature theorem is being transcribed.

## Degenerate cases

At `r = 0` the only word is empty, so `T₀F = ‖F‖` pointwise and the estimate
holds with `C = 1`. At `d = 0` the space is a single point, the closed ball is
the whole space, and for `r > 0` there are no words, so the left side is zero.
These cases are part of the statement, not excluded by a hypothesis.

## Status

This statement alone proves no coercive estimate. Cutoff commutators,
radius-gap estimates, factorial induction, analyticity, coordinate transport
to a general normed space and automorphic growth remain separate obligations.

Worker 94 authored this statement and its initial exposition. Worker 1102
checked it and added the symbol-convention and degenerate-case explanations.
