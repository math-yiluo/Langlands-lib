# Norm-convergent monomial expansion target

Authors: Worker 36 (original construction), Worker 56 (coefficient generalization).

`Langlands.Analytic.StrictTateAlgebra.MonomialExpansionStatement` is a
proposition definition. It states that every restricted series over a
complete ultrametric normed commutative coefficient ring is the sum of its
actual coefficient monomials. `HasSum` uses finite partial sums indexed by
all finitely supported exponent functions; convergence is in the previously
constructed Gauss norm. The variable type and coefficient ring have
independent universes. No nontriviality, norm-one, multiplicativity of the
coefficient norm, or finiteness of the variable type is assumed.

The target is derived from the convergent-series description in the retained
Berkovich-course notes, Section 2.1 p.1 and Section 2.2 pp.2-3, at radius one.
The source describes finite-variable series over a nonarchimedean field and
one-variable restricted series over a commutative Banach ring. This target
expresses the norm convergence of that series description and extends the
same cofinite restriction to arbitrary variable types. It does not identify
an alternative infinite-variable analytic algebra. Completeness is an
explicit hypothesis and no conclusion is assumed as input.

The exact registered source is
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
These are undated notes of part of Vladimir Berkovich's course, note-taker
unidentified; retained as `literature/Retained original of Berkovich's Affinoid
algebras course notes (14 pages).pdf`.

The statement imports the monomial/coefficient definitions and their
intrinsic bounds, together with Mathlib. It does not import its proof,
Tate evaluation, Weierstrass division, or any affinoid construction.
