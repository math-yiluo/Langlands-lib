# Descent of the twisted centralizer at an exact regular norm

Fix a field `F`, commutative `F`-algebras `R` and `S`, and an injective
`F`-algebra map `f : R → S`. Let `σ` be an `F`-automorphism of `S` with
`σ ^ l = 1` whose fixed scalars are exactly the image of `f`. Suppose the
ordered cyclic norm of `δ ∈ GL_n(S)` is the image of a regular semisimple
`g ∈ GL_n(F)`.

The cyclic norm identities show that `δ` and every element of its twisted
centralizer commute with the image of `g`. The published cyclic-vector
argument makes this ordinary centralizer commutative over `S`. As a result,
within the ordinary centralizer the twisted centralizer equation reduces to
entrywise invariance under `σ`.

`exactRegularNormCentralizerEquiv` extends coefficients from the ordinary
centralizer in `GL_n(R)`. For surjectivity, both a fixed matrix and its
inverse have entries in the image of `f`. Injectivity of `f` reflects the
inverse and centralizer identities. The resulting multiplicative
equivalence has the stated matrix map as its forward function.

This algebraic construction extends the exact-norm comparison used in
Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula*, Chapter 1, §1 and Lemma 1.1, pp. 3–4, to the coefficient
rings needed for the adelic application. Its formal proof uses explicit
matrix centralizer coordinates and the supplied fixed-scalar property.
