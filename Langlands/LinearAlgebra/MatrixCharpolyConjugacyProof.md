# Finite codes for conjugacy classes with prescribed characteristic polynomial

`Langlands.matrixCharpolyFiniteConjugacy.{uK}` proves the unchanged proposition
`Langlands.MatrixCharpolyFiniteConjugacyStatement.{uK}`. For every field `K`,
natural number `n` and polynomial `c`, it produces a finite set of square
matrices meeting the conjugacy class of every matrix with characteristic
polynomial `c`. Conjugation has the stated direction `g * x * g⁻¹ = y`, with
the inverse taken in `Matrix.GeneralLinearGroup (Fin n) K`.

For nonzero `c`, Mathlib's `Polynomial.fintypeSubtypeMonicDvd` makes the type of
monic divisors of `c` finite. Codes are ordered tuples of such divisors with
length at most `n`. The cyclic product associated to a code determines a
polynomial-module isomorphism class. The subtype of codes realized by matrices
with characteristic polynomial `c` is finite. Classical choice selects a
matrix realizing each such code, and their image is the required finite set.

Cayley–Hamilton annihilates every matrix in the specified fiber: the proof uses
`Matrix.charpoly_mulVecLin` and `LinearMap.aeval_self_charpoly` for its
endomorphism of `Fin n → K`. Applying
`polynomialModuleBoundedCyclicDecomposition` to this vector space supplies
a cyclic-product equivalence with monic divisors of `c` and a length bounded
by its dimension. `Module.finrank_fin_fun` identifies this dimension with `n`,
so this is a realized code. Composing its cyclic-product equivalence with the
inverse equivalence for the chosen representative yields an equivalence of
their polynomial modules. The imported `matrixAEvalConjugacy` gives the
conjugating matrix.

For `c = 0` the fiber is empty because characteristic polynomials are monic
and nonzero, so the proof uses the empty finite set. The argument includes
`n = 0`, when every permitted code has length zero, and fields of arbitrary
characteristic. All choices are classical; the resulting finite set need not
consist of distinct conjugacy classes.

This is an internal linear-algebra proof of the prerequisite described in the
statement's Markdown, which explains its role in the direct constructiveness
argument motivated by Bernstein–Zelevinsky (1976), Remark 7.4. The implemented
argument uses bounded ordered tuples and the two imported Library theorems
`polynomialModuleBoundedCyclicDecomposition` and `matrixAEvalConjugacy`.
