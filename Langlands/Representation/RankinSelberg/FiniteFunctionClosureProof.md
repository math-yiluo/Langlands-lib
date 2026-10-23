# Proof of finite-function closure

`Langlands.RankinSelberg.finiteFunctionClosure` proves the published
`FiniteFunctionClosureStatement G H` with independent universes for the monoids
and arbitrary supplied topologies.

The implemented proof uses the equivalence between finite generation and finite
dimensionality for complex submodules. The translate of a product belongs to
the product of the two translation spans. Mathlib's `Submodule.FG.mul` makes
that containing submodule finitely generated, and `Submodule.FG.of_le` passes
finite generation to the translation span of the product.

For pullback, precomposition with the given continuous monoid homomorphism is
a complex linear map between function spaces. The homomorphism law places each
translate of the pullback in the image of the original translation span. That
image is finitely generated, and again the submodule inclusion gives the
required finite generation. Continuity follows by composition.

For a complex-valued monoid homomorphism, each translate is its value at the
translating element times the homomorphism as a function. Thus the translation
span is contained in the span of that single function. The singleton span is
finitely generated. Product continuity and the supplied character continuity
complete the remaining clauses.

This is an internal linear-algebra proof. It does not use a Whittaker expansion,
a character decomposition, Haar integration, or analytic continuation. Its
scope is exactly the three closure clauses; the particular modulus character
and the full JPSS analytic conclusions remain separate.
