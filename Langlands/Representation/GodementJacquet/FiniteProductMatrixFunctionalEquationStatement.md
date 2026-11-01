# Conditional existence on a finite normalized product

`Langlands.GodementJacquet.FiniteProductMatrixFunctionalEquationStatement`
asserts closure of normalized matrix functional-equation data under a finite
actual normalized upper block product. The canonical p-adic field and the
block carriers have independent universes. The total rank is positive, all
block ranks are positive by `BlockShape`, and the blocks are supplied as
bundled smooth complex representations.

The premises are admissibility of every block, a continuous unit-valued
scalar central quasicharacter for every block, the supplied nontrivial unitary
additive character and self-dual scalar additive Haar measure, and existence
of full normalized matrix data on every block. The conclusion is existence of
such data on the actual `canonicalNormalizedProductInduced` representation.
Neither the blocks nor the induced representation are assumed irreducible.
The assertion is conditional on the full block data.

The internal predicate `Padic.HasNormalizedMatrixFunctionalEquationData`
expresses existence of the two polynomials, complex unit and integer exponent
in the existing `Padic.NormalizedMatrixFunctionalEquationData`. At actual rank
`n+1` it is precisely that existential statement. At rank zero it is `False`,
which keeps rank zero outside its scope without choosing a predecessor or
transporting the representation along an arbitrary equality.

The unchanged data predicate retains both common convergence half-planes,
rational continuations of every actual test and bi-smooth coefficient pair,
both normalized Laurent-span generators with polynomial constant coefficient
one, and Fourier witnesses before all coefficients and continuation pairs.
The actual square product of the supplied scalar measure, plus transpose
Fourier pairing, inverse-transpose coefficient, normalized shift, spectral
variable, central scalar one and sign exponent zero all remain those of the
imported predicate.

This is an internal derived statement. Its intended justification is induction
on the number of ordered blocks, using the published actual
`headTailProductInductionEquiv`, the conditional
`twoBlockMatrixFunctionalEquationInduction`, and equivalence transport of full
normalized data. The singleton case is the actual single-block evaluation
equivalence. Finite external tensor admissibility, normalized induction
admissibility and the product scalar-character theorem provide the structural
hypotheses at each step. These published results provide the provenance of the
closure assertion; this file introduces no new analytic existence premise or
unconditional reducible functional-equation claim.

This module states the proposition and defines the rank-indexed existential
predicate. It proves neither the closure assertion nor the irreducible generic
functional-equation theorem. Analytic bases remain separate obligations.
