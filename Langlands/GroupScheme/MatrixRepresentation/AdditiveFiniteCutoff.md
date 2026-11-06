# Finite degree cutoffs for full additive coefficient algebras

This internal derived unit uses the actual additive coefficient algebras from
`AdditiveTensorAlgebra` and the density consequence in
`AdditiveGeneratedFullness`. The field has arbitrary universe `u`, the supplied
additive-family index has independent universe `v`, and each finite decidable
coordinate type lies in `Type`. No finiteness assumption on the family index
is required.

The truncated coefficient algebra is monotone in its strict degree bound.
`boundedCoefficientAlgebra` is the subalgebra whose elements lie in some
truncated coefficient algebra. For sums and products a common bound is the
maximum of the two supplied bounds. Every truncated algebra lies in the full
coefficient algebra, and every full generator in degree `d` lies in the
truncation below `d + 1`. Algebraic generation therefore identifies the bounded
union with the full coefficient algebra.

If the full algebra is all matrices, each elementary matrix with entry one lies
in some truncation. There are finitely many pairs of coordinates, so the finite
supremum of their bounds puts every elementary matrix in a single truncation.
Expanding an arbitrary matrix as a sum of scalar multiples of these elementary
matrices proves that truncation is full. This proof also covers empty coordinate
types, for which the finite supremum is zero.

For a prime natural number `p`, every exponent `e` at least this degree cutoff
satisfies `N ≤ e < p^e`. Monotonicity thus gives full coefficients below `p^e`
for every sufficiently large exponent. This algebraic part needs neither a
characteristic assumption nor a perfect or algebraically closed field.

For the ambient application, assume the field is algebraically closed of prime
characteristic `p` and the actual ambient group is affine, reduced, and locally
of finite type. Supply a family of additive-group morphisms that geometrically
generates the ambient group. For an actual irreducible first representation on
nonempty finite coordinates, `AdditiveGeneratedFullness` supplies full
coefficients. The finite-cutoff result supplies one exponent bound depending on
this first representation and the supplied family. For every larger exponent
and every actual irreducible second representation on nonempty finite
coordinates, the existing actual tensor criterion proves irreducibility of the
entire original `ρ.tensor (σ.frobeniusPower p e)`. The exponent bound is
quantified before the second coordinate type and representation. Irreducibility
uses the existing all-affine-test stability predicate, including nonreduced test
algebras. A final corollary chooses such an exponent above any requested lower
bound by taking a maximum.

This result supplies eventual Frobenius tensor irreducibility for supplied
irreducible factors and supplied geometric generation. It constructs no
generating root family, highest-weight or Steinberg representation, Borel or
maximal torus, or big-cell decomposition, and makes no entire induced-space
comparison. It does not prove `SteinbergBigCellStatement`.
