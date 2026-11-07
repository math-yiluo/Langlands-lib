# Rational conjugation of actual additive coefficient operators

This internal derived unit works over any field with a finite matrix
representation of an actual group scheme. `VectorGroup.conjugateMap x g`
postcomposes a supplied additive group map `x` with the actual inner scheme
automorphism of a supplied rational point `g`. Its point formula holds on
every relative test scheme.

If `g` normalizes a supplied torus inclusion through an actual torus automorphism
`sigma`, and `x` has the full all-test equivariance character `alpha`, the
conjugated map has character `characterAut sigma alpha`. The proof pulls back
the torus point by `sigma` inverse and applies the original equivariance law.
It preserves the contravariant character convention of the Library.

In any finite matrix representation, the conjugated additive matrix
intertwines with the original matrix through the constant matrix of `g`, over
every commutative test algebra. Evaluating this identity over the polynomial
algebra at its universal variable and comparing coefficients proves the same
identity for every original divided-power coefficient matrix. Thus the
degree-`m` conjugated coefficient on `rho(g) v` equals `rho(g)` applied to the
degree-`m` original coefficient on `v`, for every vector and natural `m`.
No infinite-field, root-system, or highest-weight hypothesis is needed.

The provenance is the actual inner scheme automorphism, the natural scalar
extension formula for rational matrices, and the definition of additive divided
powers as polynomial coefficients. No external source is invoked. This
transport result supplies no ordered enumeration of roots or top-action
nonvanishing on its own.
