# Determinant Euler polynomial and rational reciprocal

Placement note (Worker 64): the canonical module is `Langlands.LocalFactor.Euler.Definitions`.
It is moved from `Langlands.LocalFactor.Euler` with every public declaration name,
namespace, type and mathematical body retained. The old module remains a thin
compatibility import. Original source references and authorship below are retained.
The [migration record](../Abelian/Definitions.md#structural-migration-record) gives the complete map and checks.


This module constructs the linear-algebra part of the nonarchimedean arithmetic
L-factor. For a finite free module and an endomorphism `A`, `eulerPolynomial A`
is the reversed characteristic polynomial. Its determinant formula is proved
for every finite basis, and its value at `z` is proved to be `det(1-z A)`.
Its constant coefficient is one, so it is a nonzero polynomial over a field.
Conjugating `A` by a linear equivalence preserves the polynomial.

Over a field, `rationalFactor A` is the reciprocal of that polynomial in
Mathlib's rational function field. It is not an everywhere finite scalar
function. `RegularPoint A` consists precisely of the scalar values where
the Euler polynomial is nonzero. `regularFactorValue` is defined only on
this subtype and takes values in the units of the coefficient field.
Zero belongs to this domain and the value there is one.
The product of `rationalFactor A` and the embedded Euler polynomial is
proved to be one in the rational function field.

For complex coefficients, `spectralParameter q hq s` is
`exp(-s log q)`, for `q > 0`. `SpectralRegularPoint` restricts to the
spectral values for which the denominator is nonzero. `spectralFactorValue`
uses the same reciprocal determinant there.
The equality of this exponential expression with complex `q^(-s)` is proved.
The intended later specialization uses the actual residue cardinality and the endomorphism
induced by geometric Frobenius on `(ker N)^I`. This module does not replace
that specialization with arbitrary invariants, nor construct a Weil group,
inertia, monodromy, local constants, or reciprocity.

## Source correspondence

John Tate, *Number theoretic background*, in *Automorphic Forms,
Representations and L-Functions*, Proceedings of Symposia in Pure
Mathematics 33, Part II (1979), sections 3.3.2 (page 14) and 4.1.6
(pages 20–21). The original defines the determinant reciprocal first in
the variable `t`, then substitutes `t=q^(-s)`. The linear-algebra
construction here abstracts that part and proves its intrinsic basis
invariance. It does not assume any of the source's functional equations.
Section 3.3 explains why factors should take values in nonzero meromorphic
functions rather than finite scalars at every point.

Registered original: `tate-1979-number-theoretic-background`.
Retained file:
`C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
Content SHA256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
Printed page `p` is PDF page `p+9`. Pages 10–21 were read, and page 21
was checked visually to verify the determinant and quotient formulas.

## Dependencies and construction proofs

There are no project mathematical dependencies. The pinned environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The implementation reuses `LinearMap.charpoly`, `Matrix.reverse_charpoly`,
`LinearMap.charpoly_toMatrix`, determinant evaluation, and
`LinearEquiv.charpoly_conj`. The remaining normalization and transport
proofs follow from these identities. The polynomial construction retains
an arbitrary commutative coefficient ring and finite free carrier; the
rational reciprocal requires a field. The spectral interpretation
specializes the coefficients to the complex numbers.

Worker 20 authored this construction. Development compilation and semantic
review status are recorded separately; this file makes no acceptance claim.
