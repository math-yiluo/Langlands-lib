# Proof that degrees of endomorphisms are polynomial along lines

Lean module: `Langlands.AbelianScheme.EndomorphismDegreeLinePolynomialProof`.

`Langlands.AbelianScheme.endomorphismDegreeLinePolynomial :
EndomorphismDegreeLinePolynomialStatement.{u}` proves the Library statement
`Langlands.AbelianScheme.EndomorphismDegreeLinePolynomialStatement` in its universe `u`.

The proof introduces the field `k`, the abelian scheme `A`, the natural number `g` and the
relative-dimension hypothesis. It takes `δ = EndomorphismEulerDegree.endomorphismEulerDegree A g`
and applies `EndomorphismEulerDegree.endomorphismEulerDegree_spec` (module
`Langlands.AbelianScheme.EndomorphismEulerDegree`), whose statement is the body of the
proposition for that `δ`. `δ(α)` is the `g`-th coefficient of the Euler polynomial
`m ↦ χ((α^* L)^{⊗m})` divided by that of `m ↦ χ(L^{⊗m})`, for a chosen ample line bundle `L`.
That module's Markdown explains the proof route: the published finite-flat Euler-coefficient
theorem handles isogenies; the theorem of the cube and a separate-polynomiality lemma
(`Langlands.Algebra.SeparatelyPolynomialQuadraticLine`) give polynomiality along lines.
The algebraic closedness of `k` is not used.

No hypothesis is added: the theorem's type is exactly the statement.
