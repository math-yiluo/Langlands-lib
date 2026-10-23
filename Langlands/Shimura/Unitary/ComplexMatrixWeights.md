# Corrected Harris diagonal matrices over complex algebras

This module computes the matrix coordinates of the actual scalar-extended
corrected Harris homomorphism. It is an internal algebraic consequence of
`ComplexMatrixCoefficients`, `RealSplitting`, `Domain`, and `Deligne`. It
retains the ordered complex factors and the corrected Harris convention.

## Diagonal construction

For a commutative ring `S`, natural numbers `n,r`, and `p : S × S`,
`ComplexMatrix.splitDiagonal S n r p` is the pair of diagonal matrices

\[
 \left(
  \operatorname{diag}(p_2\text{ for }i<r;\ p_1\text{ otherwise}),
  \operatorname{diag}(p_1\text{ for }i<r;\ p_2\text{ otherwise})
 \right).
\]

The indices are `Fin n`. All off-diagonal entries are zero. The generic
definition does not require `r ≤ n`; it simply uses the displayed comparison
of the index with `r`.

## Actual Harris scalar extension

The specialization retains the hypotheses of `HarrisSignatureCharts`: number
fields `E` and `K`, respectively totally real and totally complex, a quadratic
extension `K/E`, the given `E`, `K`, and rational algebra structures on `A`
with the tower `ℚ → E → A`, the second-kind involution, and actual compatible
charts `C` with distinguished real place and chosen complex embeddings. A
finite `E`-basis `b` of `A` is supplied. Let `S` be any commutative complex
algebra with a compatible specified real algebra structure. No reducedness,
field, or finite-dimensional hypothesis on `S` is required.

For a real embedding `τ`, put `rτ = n-1` at the distinguished place and `rτ = n`
elsewhere. Write `h = C.realComplexHom b` and let `e` be
`C.iteratedScalarMatrixEquiv b S`. For every quadratic element
`q : DeligneTorus.Complexification S`, `deligneAlgebraMap_matrix` proves

\[
 e(h.\mathrm{deligneAlgebraMap}_S(q))_\tau
   = \mathrm{splitDiagonal}_{n,r_\tau}
      (\mathrm{DeligneTorus.splitEquiv}_S(q)).
\]

The left side is an element of the actual scalar extension
`S ⊗[ℝ] (ℝ ⊗[ℚ] A)`, expressed in the constructed Harris matrix coordinates.
The ordered split scalars are

\[
 p_1=q_{\mathrm{re}}+q_{\mathrm{im}}j(i),\qquad
 p_2=q_{\mathrm{re}}-q_{\mathrm{im}}j(i),
\]

where `j : ℂ → S` is the algebra map. The Lean proof expands the quadratic
map as `q.re ⊗ 1 + q.im ⊗ h(i)`, applies the two pure-tensor formulas, and
uses the published corrected diagonal formula for `h(i)`. It then checks
diagonal and off-diagonal entries and the two signature blocks. In particular,
complex conjugation is applied only to original matrix entries and never to
the coefficient ring `S`.

For a quadratic unit `q`, `delignePoints_matrix` states the same formula for
the underlying matrix unit of the constructed similitude
`h.delignePoints S q`. The pair on the right is the underlying scalars of
`DeligneTorus.splitPointsEquiv S q`.

`delignePoints_firstFactor` evaluates this at the inverse image of `(u,1)`
under the split unit equivalence, for every `u : Sˣ`. It gives

\[
 \bigl(\operatorname{diag}(1\text{ for }i<r_\tau;\ u\text{ otherwise}),
       \operatorname{diag}(u\text{ for }i<r_\tau;\ 1\text{ otherwise})\bigr).
\]

Thus the powers of `u` are zero and one on these respective blocks.
`delignePoints_secondFactor` evaluates the inverse image of `(1,u)` and
interchanges the two matrices. Both formulas follow from the quadratic-unit
formula and cancellation of the split equivalence with its inverse.

## Provenance and scope

The proof uses only the already constructed Harris real map, its published
corrected matrix formula, the actual quadratic scalar-extension map, and the
ordered matrix equivalence over `S`. It assumes no matrix-weight comparison
as input and uses no additional external existence theorem.

These are algebraic formulas for the constructed Deligne map on all
commutative complex coefficient algebras. The module does not yet connect
them to the categorical point comparison of the published cocharacter on
every complex test scheme. It does not establish the inverse Kottwitz weight
formula, chart independence, conjugacy, reflex-field comparison, smoothness,
reductivity, or the PEL geometry and coefficient descent. Those remain
obligations of the host task.
