# Automorphism covariance of the compact stages integral

`SplitStagesCompactEvalCovariance` compares two evaluations of the actual
`splitStagesCompactEquiv`. The theorem assumes that the compact sections
are related by inverse pullback and a linear coefficient operator, and that
the latter descends to the intersection coinvariants. The evaluation points
`x y : L` range over the ambient quotient group. The ambient automorphism
`α` and section `s` satisfy `α (s y) = s x`. The inverse automorphism on the
inner quotient preserves the supplied measure.

At a kernel representative `t`, the integrand is the coinvariant class of
the section value at `t * s(x)`. The ambient inverse sends this product to
the product of the inverse kernel representative and `s(y)`. Extensionality
on the quotient identifies the new simple function with the inverse
pullback followed by the descended coefficient operator. The proof uses
finite measure on compact sets, change of variables, and linearity of the
algebraic integral to commute the operator with integration.

This calculation supplies the compatibility with the twisted action on a
fixed Bruhat piece in the Jacquet calculation of Rogawski, *Trace Paley-Wiener
theorem in the twisted case* (1988), proof of Lemma 8.1, printed p. 222. The
implementation works directly with the finite-fiber integral in the compact
stages comparison.
