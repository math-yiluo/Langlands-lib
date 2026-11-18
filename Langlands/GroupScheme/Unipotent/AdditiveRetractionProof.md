# Retraction onto a closed additive line

`Langlands.GroupScheme.elementaryUnipotentAdditiveRetraction.{u}` proves
`Langlands.GroupScheme.ElementaryUnipotentAdditiveRetractionStatement.{u}`.

The composite of the two closed immersions gives a closed embedding of
`𝔾ₐ` into the ambient standard vector group. Its coordinate pullback is
surjective, so at least one coordinate pulls back to a nonzero polynomial.
The coordinate pullbacks are additive, and additive polynomials remain
additive under this substitution. In the univariate coordinate ring of
`𝔾ₐ`, choose a nonzero pullback of an additive polynomial of least degree.
The proof divides each coordinate pullback by the chosen polynomial using
`TorusLinearization.IsAddPoly₁.exists_comp_add`. Each remainder is itself a
pullback of an additive polynomial and vanishes by minimality.

The pullback thus factors through evaluation at the chosen polynomial.
Surjectivity gives a polynomial in that element equal to `X`. The degree
formula for composition forces the chosen polynomial to have degree
one. Its constant coefficient is zero by additivity. Scaling its lift
by the inverse of its linear coefficient produces an additive polynomial
on the ambient vector group whose pullback is `X`.

The primitive family defined by this polynomial gives the actual
homomorphism from the ambient vector group to `𝔾ₐ`. The composite on
coordinate algebras fixes `X`, hence is the identity. Restricting this
homomorphism along the given embedding of `G` gives the required retraction.

The target is Milne, *Algebraic Groups* (2017), Corollary 14.47, printed
p. 295, registered as `milne-2017-algebraic-groups` with SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Milne proves the corollary via the equivalence in Theorem 14.46. The Lean
proof uses the right-division argument for additive polynomials discussed
before Proposition 14.50 on printed p. 296. The division theorem used
here requires prime characteristic and applies over imperfect fields.
