# Uniform annihilators without fixed exponent labels

This derived module allows the finite expansion into simultaneous generalized
eigenfunctions to vary with its parameter. It removes the need to choose fixed
global exponent labels and a parameter-independent unitary classification.

`padPolynomialDegree p N z` multiplies a polynomial by a power of `X-z` to reach
degree `N` when the original degree is at most `N`. The added roots are only `z`,
and a polynomial annihilator remains an annihilator after this multiplication.

Independent joint generalized eigenspaces imply that the nonzero components of
a finite expansion in a finite-dimensional stable space are linearly independent
when one nonzero vector is selected from each occurring character. Hence the
expansion's support cardinality is bounded by the dimension.

For a parameter-dependent expansion with at most `n` summands and common
nilpotence order `d`, take the product of `(X-χ(a))^d` over the weak summands and
over the positive summands separately. Their degrees are at most `n*d`. The
existing weak/positive decomposition identifies these sums with the actual
`weakPart` and `positivePart`. Pad the weak polynomial using root one and the
positive polynomial using root zero. Both degrees become exactly `n*d`; the
weak roots still have norm one and the positive roots are still bounded by the
supplied nonnegative `θ < 1`. Every parameter may have a different support and
unitary classification. Coincident specialized characters are permitted.

The result is the existing `HasUniformSplitAnnihilators` property. Uniform
nilpotence, the summand-count bound and the nonunitary root bound remain inputs
to this abstract adapter and must be proved for the actual orbit family.

The context is Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), source `waldspurger-2003-plancherel`, the exponent
polynomials in the proofs of VI.2.1 and VI.2.3, printed pp.297–300. This variant
is an internal alternative to the fixed-label packaging; it uses elementary
finite-dimensional independence, polynomial padding and the published weak-part
projection APIs.
