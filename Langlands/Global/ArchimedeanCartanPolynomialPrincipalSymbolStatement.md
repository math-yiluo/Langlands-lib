# Principal symbol of the actual monic Cartan polynomial operator

`Langlands.Global.ArchimedeanGL.CartanPolynomialPrincipalSymbolStatement K n`
is a proposition definition, for an arbitrary number field `K : Type u` and
every natural rank `n`, including zero. Write `E = ArchimedeanMatrix K n`,
`d = cartanCoordinateDimension K n` (the real dimension of `E`) and
`D_p = cartanPolynomialCoordinateOperator K n p`. The proposition asserts:

```text
for every monic p : Polynomial ℂ, every y : E and every ξ : E →L[ℝ] ℝ,
  D_p.principalSymbol y ξ = (ambientCartanCovectorForm K n y ξ : ℂ) ^ p.natDegree.
```

## The two sides

The operator `D_p` is the published coefficient construction of
`Langlands.Global.ArchimedeanCartanPolynomialCoefficients`, unchanged. It has
declared order `2 * p.natDegree`, the fixed real basis `cartanCoordinateBasis K n`
of the original normed matrix space, and the explicit recursive complex
coefficient arrays. No replacement operator, existential choice of operator or
assumed symbol certificate occurs.

The left side is the published `CoordinateScalarOperator.principalSymbol` of
`Langlands.Analysis.CoordinateScalarDifferentialOperator`. Writing
`N = 2 * p.natDegree` and `e_j = cartanCoordinateBasis K n j`, it is

```text
Σ_(w : Fin N → Fin d) D_p.coefficient (Fin.last N) w y * Π_(j : Fin N) (ξ (e_(w j)) : ℂ).
```

Only the coefficients of the top declared order `N` enter, with ordered words
that may repeat letters. There is no factor of `i`. The second Lean `example`
checks this unfolding by `rfl`.

The right side is the complex embedding of the real number
`ambientCartanCovectorForm K n y ξ` from
`Langlands.Global.ArchimedeanCartanSymbolBounds`, raised to `p.natDegree`. That
form is the full real Cartan sum of squares

```text
Σ_(i : CartanBasisIndex K n) (ξ (y * realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i)))^2,
```

over every member of the published real Cartan basis. The third Lean `example`
checks by `rfl` that the summand is `ξ (cartanMatrixField K n i y) ^ 2`, the
covector evaluated on the matrix field used by the coefficient recursion.

## Scope

The matrix `y` ranges over all of `E`; it need not be invertible. Every real
continuous covector `ξ` is allowed, with the original operator norm and topology
on `E` and its continuous dual. All real directions are kept, including both
real directions at each complex infinite place. Coefficients and the symbol are
complex valued. The universe of `K` is arbitrary.

The only hypothesis on `p` is monicity, which fixes its leading coefficient to
one; the zero polynomial is therefore excluded, while the constant monic
polynomial `1` is included. In that case the declared order is zero, the symbol
is the coefficient at the empty word, and the asserted right side is `q ^ 0 = 1`.
No positive degree, positive rank, nonempty basis or nonzero covector is assumed;
rank zero and an empty Cartan index are allowed. In particular, at `ξ = 0` with
positive degree the asserted value is zero.

At an actual unit `g`, the fourth Lean `example` shows that the proposition
yields the symbol clause of
`CartanPolynomialCoordinateRealizationStatement K n` for the specific operator
`D_p`. The present statement is stronger in that clause, because it holds at
every ambient matrix rather than only at units. It says nothing about the other
two clauses of that statement.

## Internal provenance

This is an internal derived statement about published constructions, not a
transcription of a theorem in the literature. It isolates the principal-symbol
correctness obligation of the explicit recursive coefficients, one of the
remaining obligations listed for the coordinate realization statement. The
analytic motivation is the elliptic route recorded in
`notes/automorphic/elliptic-analyticity-source-map.md`; no external theorem is
cited as formalized here.

A proof is expected to follow the recursion. For a left directional composition
with a field `V`, the top-order coefficient is the old top coefficient on the
tail of the word times the coordinate `v_(w 0)(y)` of `V y`, because the
differentiated-coefficient term has no entry above the old order. Summing over
the first letter gives `ξ (V y)` times the old symbol. Two compositions with the
same Cartan field, summed over the Cartan index, multiply the symbol by the form
above. Induction gives its `m`-th power for the `m`-th iterate. In the polynomial
sum, iterates of index `m < p.natDegree` are zero-padded at the top order, and
monicity gives coefficient one to the highest iterate. These are proof
obligations; this file does not prove them.

## Not asserted

The file defines a proposition and checks it only by elaboration and the
unfolding examples above. It proves neither this proposition nor coefficient
analyticity, equality of the coordinate action with the ambient Cartan
polynomial, ellipticity, local coercive bounds, analytic elliptic regularity or
joint-finite analyticity.

Worker 116 supplied the statement draft and its proof route. Worker 880 checked
the proposition telescope against the published carriers, added the unfolding
examples and prepared this pair for independent review.
