# Polynomial Xi bounds along actual strict component rays

`HasPolynomialXiComponentRayBound` specifies a bound for Xi at each
positive power of a fixed component point, by the corresponding power of
the norm of its radical half-modulus times `C * (1+n)^d`. The theorem derives
it for every strict intrinsic section ray from the separately owned upper
spherical-function statement. This is the growth input for the normalized
Jacquet exponent argument.

The existing standard-component chamber theorem expresses every power of
the specified point as a uniformizer cocharacter value which annihilates
the target Levi's selected roots and is nonnegative on all simple roots.
The original simultaneous standard basis supplies a compatible component
for the minimal Levi; the same existing chamber comparison places those
powers in its weak section chamber. Thus the published upper-bound
proposition, retained as an explicit unproved input here, applies with one
degree and constant for every power.

Centrality of the component in the actual target Levi makes its intrinsic
minimal modulus one. The exact ambient modulus factorization therefore
identifies the ambient minimal modulus with the target radical modulus.
The half-modulus is multiplicative, giving its original value to the power
`n`. Subadditivity and nonnegativity of the actual matrix height bound its
remaining factor by a constant times `(1+n)^d`.

The contextual original source is Waldspurger, *La formule de Plancherel pour
les groupes p-adiques, d'après Harish-Chandra* (2003), Lemma II.1.1, printed
p.251, and the proof of Proposition III.2.2, printed p.266, source
`waldspurger-2003-plancherel`. The actual-component specialization is derived
project content. This module does not prove the upper Xi proposition.
