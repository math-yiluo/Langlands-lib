# An injective one-parameter normalization of continued Eisenstein forms

Start with a finite basis of continued functions with local holomorphic
numerators, a common growth-space normalization on a ball around the
specialization parameter, and an injective member on the regular locus.
The meromorphic determinant argument supplies an injective member in
the dense open regular set of the ball. The common denominator is
nonzero there, so the normalized member is also injective.

Take the complex affine line from the specialization parameter to
that regular point. `normalizedAutomorphicLineDomain` is the preimage of
the normalization ball on this line. It is open and convex over
\(\mathbb R\), hence preconnected. It contains zero, and the preimage of
the regular set contains one. Weak holomorphy on the line follows by
composition. If each original basis function is automorphic on the
regular set, the scalar automorphic submodule also contains every
normalized linear combination there.

At each order the linear Taylor map takes values in the actual stable
matrix automorphic module of \(GL_n\). Its evaluation at an adelic point
is the corresponding scalar derivative on the line at zero, divided by
the factorial of the order.

This is an internal implementation of the passage to one complex
parameter in Langlands, *On the notion of an automorphic representation*
(1979), proof of Proposition 2 and Lemma 9, printed pp. 205–207
(Corvallis Part I PDF pp. 200–202).
