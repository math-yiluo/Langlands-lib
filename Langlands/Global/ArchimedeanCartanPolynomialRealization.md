# Coordinate realization of monic Cartan polynomials

For every number field in any universe and every natural rank, the theorem
`cartanPolynomialCoordinateRealization` proves the independently published
proposition `CartanPolynomialCoordinateRealizationStatement`.
It chooses the actual `cartanPolynomialCoordinateOperator`, with the published
fixed real basis and order twice the polynomial's natural degree. This one
operator is chosen before any function, unit or covector.

The coefficient analyticity proof shows that every coefficient is real analytic
on the full original ambient matrix space, hence on the open units domain.
The action proof applies on any open smooth domain, and is specialized here to
the range of the unit inclusion. The principal-symbol proof applies at every
ambient matrix and every real continuous covector; at units it gives the stated
power of the actual ambient Cartan covector form for a monic polynomial.
The three imported helper modules document their respective recurrence,
product-rule and top-order arguments.

The proof retains the original matrix norm and topology, real derivatives,
complex coefficients and values, arbitrary universes, rank zero and constant
monic polynomials. It makes no claim of analytic regularity for solutions,
polynomial annihilation or completion of the joint-finite analyticity theorem.
Its provenance is internal correctness of the explicit published construction.

## Declaration and proof assembly

The theorem
`Langlands.Global.ArchimedeanGL.cartanPolynomialCoordinateRealization` has
type `CartanPolynomialCoordinateRealizationStatement K n`, for all
`(K : Type u) [Field K] [NumberField K]` and `n : ℕ`. That statement is the
proposition published in
`Langlands.Global.ArchimedeanCartanPolynomialRealizationStatement`, which this
module does not modify. Given a monic `p`, the proof supplies the following
witnesses:

- the dimension `d = cartanCoordinateDimension K n`;
- the operator `D = cartanPolynomialCoordinateOperator K n p`.

It then proves the three conjuncts.

1. `cartanPolynomialCoordinateOperator_analyticCoefficients K n p` gives
   analyticity on `Set.univ`. The published lemma
   `CoordinateScalarOperator.AnalyticCoefficientsOn.mono` restricts it to the
   range of `Units.val`.
2. `cartanPolynomialCoordinateOperator_action` gives the action equality. It is
   applied with `S` equal to that range, which is open by
   `Units.isOpenEmbedding_val.isOpen_range`, and at the point `g` with
   membership witness `⟨g, rfl⟩`.
3. `cartanPolynomialCoordinateOperator_principalSymbol` gives the symbol
   equality, applied at the matrix underlying `g` and using monicity.

Every declaration in this module and its three helper modules uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Worker 116 authored this module and the three helper modules. Worker 880
checked them and prepared them for review.
