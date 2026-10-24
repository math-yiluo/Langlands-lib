# Galois transport of actual complex group points in matrix coordinates

This internal construction connects `GaloisChartComparison` to actual complex
points of the rational Harris group scheme. It retains a central simple
unitary datum `D`, all its number-field, algebra and scalar-tower hypotheses,
actual Harris signature charts `C`, and a compatible CM section `hΦ`.
The finite totally real basis is `D.totallyRealBasis`.

`complexEmbeddingPointMatrices` is a monoid homomorphism from actual
`Spec ℂ`-valued points of `D.rationalGroupScheme` over `Spec ℚ` into the
product of matrix rings indexed by embeddings `i : K →+* ℂ`.
It first uses `D.rationalAffinePointsEquiv` to obtain a scalar-extended
similitude, takes its underlying algebra unit and its value in `ℂ ⊗[ℚ] A`,
then applies the constructed `C.embeddingMatrixEquiv`.
All maps in this composite preserve multiplication and the unit.
The output entries are matrices; this definition does not assert that
arbitrary arrays of matrices arise from group points.

`complexPointMultiplier` takes the common scalar unit recorded in the same
similitude. `complexEmbeddingPointCoordinates` pairs the matrix array with
this multiplier as a monoid homomorphism. The theorem
`complexEmbeddingPointCoordinates_injective` proves that the pair determines
the original scheme point. Equality of the arrays and injectivity of the
matrix splitting recover the underlying algebra units. Equality of the
multipliers then recovers the pair defining a similitude; injectivity of
the affine point equivalence finishes the proof. No surjectivity onto the
entire product is claimed.

Write `M(x)` for the matrix array, `c(x)` for the multiplier, `T_s` for the
full matrix action and `E_(s,i)` for the constructed complex-linear chart
comparison. The Galois formulas are

\[
\begin{aligned}
 M(s\cdot x)&=T_s(M(x)),\\
 M(s\cdot x)(s\circ i)&=E_{s,i}\bigl(S_s(M(x)(i))\bigr),\\
 c(s\cdot x)&=s^\times(c(x)).
\end{aligned}
\]

Here `s` is an arbitrary rational algebra automorphism of the complex
numbers, `s·x` is `D.complexPointGaloisAction s x`, and `S_s` applies `s`
entrywise. The first proof uses the published scheme-point coordinate
identity, the underlying tensor coefficient formula, and the intertwining
identity for the actual matrix splitting. The factor formula then uses
`embeddingMatrixGaloisEquiv_chartComparison`. The multiplier proof uses
the corresponding published coefficient-automorphism formula.

`directComplexCocharacterValue_galois_matrices` specializes the factor
formula to any actual cocharacter `χ` of the direct rational-to-complex
pullback group. For a complex unit `u`, evaluate the transported
cocharacter at `u`. Its matrix in factor `s∘i` is `E_(s,i)` applied to
the entrywise `s` transform of the matrix of `χ` evaluated at
`s⁻¹(u)` in factor `i`. The proof substitutes
`directComplexCocharacterValue_transport` into the point formula.
It retains the actual spectrum-map transport and the inverse on the
cocharacter argument.

The provenance is entirely the existing affine point equivalence, the
similitude projections, and the constructed matrix transport. This module
does not identify scheme morphisms from equality on complex points or
assert innerness of the chart comparisons. The iterated-model exact
evaluation theorem and the reflex-stabilizer comparison remain separate.
