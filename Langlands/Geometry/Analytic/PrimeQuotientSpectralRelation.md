# Spectral relations lifted through genuine prime quotients

Author: Worker 56.

For a presented strict affinoid algebra P over a complete, nontrivially
normed ultrametric field and an actual prime ideal I of P, the construction
produces a monic polynomial over the original finite-variable Tate algebra.
Its coefficients have Gauss norms at most one, and its evaluation at the
specified element of P lies in I. The only spectral premise is that all
bounded multiplicative seminorms on P take that element to at most one.

The proof first applies the proved Noetherian Banach closed-ideal theorem.
Consequently the actual ring quotient P/I carries its quotient norm and is
a complete normed domain. Its actual bounded quotient map pulls spectrum
points back to P, so the spectral premise descends.

Normalization is constructed for the composite map from the original
Tate presentation to P/I. The refined normalization theorem retains an
actual Gauss-isometric map from the smaller Tate algebra into the original
Tate algebra. The domain minimal-polynomial theorem bounds every
coefficient of the minimal polynomial of the quotient element. Mapping
this polynomial along the retained embedding preserves those bounds
exactly. Its evaluation maps to zero in P/I, giving membership in I.

In particular this does not assume that the quotient map has an algebra
section, that a relation has bounded lifts, or that an ideal is closed.
The relation remains over the original Tate algebra; this permits
products of relations for different prime ideals before passing back to P.

This is the prime-quotient component of the argument for Proposition
2.6.4, pages 11–12, and Proposition 2.6.5, page 12, of the retained
Berkovich-course notes. It uses the constructed normalization of
Proposition 2.4.1, page 6, and the closed-ideal result of Proposition
2.3.4, page 6. The Lean implementation retains the ambient embedding
explicitly to justify coefficient lifting.

Source: `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
retained PDF SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
