# Perfect-field transport of actual Frobenius coefficient fullness

This internal derived unit transports fullness of the actual additive-family
matrix coefficient algebra through Frobenius. The field has arbitrary universe
`u`, the family arbitrary index universe `v`, and coordinates are finite decidable
types in `Type`.

`scalarPreimage f A` is the matrix preimage of a `k`-subalgebra `A` under the
entrywise map of a scalar ring endomorphism `f : k →+* k`. It is again a
`k`-subalgebra because entrywise mapping preserves addition and matrix
multiplication, and sends a scalar matrix with entry `c` to the scalar matrix
with entry `f c`. The entrywise map is not asserted to be `k`-linear.

For a supplied family of actual additive-group representations in prime
characteristic `p`, every matrix in the original coefficient algebra has its
entrywise `p^e`-Frobenius image in the coefficient algebra of the actual
Frobenius-powered family. The proof uses the exact coefficient formula in
degree `p^e * d` to put each original generator in the appropriate preimage
subalgebra. The universal property of algebraic generation gives the whole
original coefficient algebra. This part does not require perfection.

If `k` is perfect in characteristic `p`, entrywise iterated Frobenius is
surjective on matrices. Therefore a full original coefficient algebra gives a
full actual powered coefficient algebra. The coefficient entries are transformed
throughout the proof; only surjectivity, supplied by perfection, removes that
transformation from the fullness conclusion.

The final theorem applies this transport to the earlier actual ambient tensor
irreducibility criterion. Its inputs are two actual ambient representations,
a supplied family of additive-group morphisms, nonempty coordinate types, full
first restricted coefficients below `p^e`, and full second restricted coefficient
algebra before Frobenius. Under perfection, the full original tensor
`ρ.tensor (σ.frobeniusPower p e)` is irreducible for stability on every affine
test algebra, including nonreduced ones.

The first truncated-fullness premise is retained without a polynomial degree
bound. No claim that restrictedness supplies it is made. Fullness of the
second algebra is also an explicit premise here. There is no root-family
construction, highest-weight or Steinberg-module existence theorem, entire
induced-space identification, or proof of `SteinbergBigCellStatement`.
