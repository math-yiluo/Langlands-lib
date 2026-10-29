# Coordinate realization and leading symbol of monic Cartan polynomials

`Langlands.Global.ArchimedeanGL.CartanPolynomialCoordinateRealizationStatement K n`
is a proposition definition. For every monic complex polynomial `p`, it asserts
the existence of a natural number `d` and one actual
`CoordinateScalarOperator (ArchimedeanMatrix K n) d (2 * p.natDegree)` satisfying
the following three properties on
`S = Set.range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)`.

- Every coefficient of `D` is real analytic near each point of `S`, expressed
  by `D.AnalyticCoefficientsOn S`.
- For every ambient function `F : ArchimedeanMatrix K n → ℂ` smooth on `S`
  and every actual unit `g`, `D.action F g = cartanAmbientPolynomial K n p F g`.
- For every actual unit `g` and every real continuous covector `ξ`,
  `D.principalSymbol g ξ = (ambientCartanCovectorForm K n g ξ : ℂ) ^ p.natDegree`.

Here `g` in an ambient expression denotes its underlying matrix. The single
operator `D`, including its finite real basis and all complex coefficient
functions, is chosen before `F`, `g` and `ξ`. No action comparison, symbol
certificate or regularity theorem is supplied as a premise of this proposition.
The only polynomial hypothesis is monicity, which fixes its leading coefficient
to be one.

The operator action and symbol are precisely the published definitions in
`Langlands.Analysis.CoordinateScalarDifferentialOperator`. The action includes
every derivative order from zero through the declared order, using real
`iteratedFDeriv` on actual basis vectors. The highest-order symbol replaces
those vectors by their evaluations under a real continuous covector and
contains no factor of `i`.

Smoothness means `ContDiffOn ℝ ∞`, using the `ContDiff` notation scope.
In pinned Mathlib, `⊤ : ℕ∞ω` is `ω` and requires analyticity; that
stronger assumption is not used.

The declaration retains every number field `K : Type u` and every natural
rank `n`. The original matrix norm, topology and real scalar structure are
unchanged. In particular, the real directions at complex infinite places are
all present. No positive rank, positive dimension, positive order, nonzero
function or connectedness assumption is added. Degree zero is included: a
monic polynomial of natural degree zero is `1`, its declared order is zero,
and the asserted symbol is `q ^ 0 = 1`. Rank zero and an empty basis are
permitted.

## Internal provenance

This is an internal coordinate realization and leading-symbol interface,
derived from the actual published constructions. It is not a verbatim theorem
in the literature.

`ArchimedeanCartanSymbol` supplies the complete real Cartan frame and the
genuine square-sum action, with the full second derivative and its first-order
moving-frame correction. `ArchimedeanCartanAmbientOperator` defines that
ambient differential expression and the polynomial sum of its iterates,
including the identity iterate. It proves their agreement on units with the
genuine enveloping powers and polynomial action. The comparison alone does
not construct finite coordinate coefficients or identify symbols of composed
operators.

`ArchimedeanCartanSymbolBounds` supplies the actual ambient covector form:
the sum of squares of the covector evaluations on the moving Cartan frame.
It proves positivity at units on nonzero real covectors, analyticity in the
matrix point, and local quadratic bounds using the original dual norm.
The present statement identifies the highest-order symbol of the entire
polynomial expression with the corresponding power of this form.

## Remaining proof obligations

A proof must construct the finite coefficient arrays by repeated directional
composition in a fixed finite real basis. The directional product rule must
account for derivatives of coefficient functions as well as new derivatives
of `F`. Applying it twice for each moving-frame direction must give the full
ambient square sum, including the first-order correction. Iteration and
zero-padding then give an operator of declared order `2 * p.natDegree`.

The proof must establish action equality for every function smooth on the
open units domain; total ambient derivatives outside that domain impose no
extra smoothness requirement. It must prove analyticity of the constructed
coefficients, including every differentiated coefficient. Finally, it must
identify the highest-order symbol of each iterate, show that lower polynomial
terms contribute nothing at the declared order, and use monicity for the
coefficient of the highest power. The zero-order and empty-basis cases must
be retained throughout these arguments.

The coefficient construction task
`da25bd78-feb3-4282-a43f-fc85a27b52e6` is a separate data construction; it
does not itself prove these correctness, analyticity or symbol assertions.
The exact proof successor to this statement must wait for its publication
and require actual publication of that coefficient construction before
submission.

This Lean file defines only the proposition. It proves no polynomial
annihilator, elliptic regularity, analyticity of a smooth solution, jet
uniqueness, density, reproduction or automorphic differential growth.

Worker 116 authored the initial Lean/Markdown pair and corrected the
smoothness notation. Worker 566 checked the declaration against the
published carriers and prepared the pair for independent review.
