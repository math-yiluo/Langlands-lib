# Moving an acting factor through an ordered group-scheme product

This internal construction isolates the algebraic scheme step in moving a
normalizing torus through an ordered product. It uses the existing actual
`AutomorphicAction.semidirectProduct` and `orderedMultiplication`. The base
scheme, acting group and finite number of factors are arbitrary; no field,
smoothness, connectedness or torus hypothesis is needed.

For actual actions of a group scheme `K` on each factor `H i`,
`suffixActionMap c p` acts on the factor coordinates with index at least `p`
and retains the acting point. It is an actual scheme morphism on
`(∏ H i) × K`. Its coordinate formulas hold on every test scheme.
`isIso_suffixActionMap` proves it is an isomorphism. On each test scheme the
inverse acts on the same suffix by the inverse acting point; the proof
establishes bijectivity for every test scheme and applies the Yoneda
isomorphism criterion.

Suppose `K` acts on an ambient group scheme `G`, and the factor inclusions
are equivariant for these actions on every test scheme.
`semidirectOrderedMultiplication a j p` inserts the acting point after the
first `p` factors. In the existing semidirect coordinates `(g,k)` its
formula is

\[
((h_0\cdots h_{p-1})\,a(k)(h_p\cdots h_{n-1}),\,k),
\]

where each factor is first mapped to `G`. This is the product of the
embedded first factors, the acting factor, and the remaining factors in
the standard law `(g,k)(g',k')=(g\,a(k)(g'),kk')`.

`suffixActionMap_comp_orderedMultiplication` identifies this actual
morphism with the suffix automorphism followed by the product of the
original ordered multiplication map and the identity of `K`.
Its proof uses equivariance separately at each factor and a finite list
induction; it never reorders the factors in `G`.
`isIso_semidirectOrderedMultiplication` then proves that insertion at any
cut is an isomorphism whenever the original ordered multiplication is an
isomorphism.

The cut is any natural number. A cut beyond the number of factors gives an
empty suffix, and zero gives an empty prefix. The empty family is included.
No bijectivity statement restricted to field-valued points is used.

The provenance is internal: the constructions and proofs follow from the
existing action laws, categorical product coordinates, finite ordered
products and the Yoneda criterion. The motivating application is the
first reduction in CGP Theorem 3.3.11, printed page 115 (PDF page 141), where
a maximal torus normalizes the semigroup factors and is moved to its
zero-weight block. This module does not construct that maximal torus or
unipotent radical, prove the requisite factor comparisons, or perform
scalar extension and descent. The full ordered semigroup product theorem
remains a separate obligation.
