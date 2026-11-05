# Conjugation maps from fixed tensors with an irreducible first factor

This internal adapter turns a nonzero fixed tensor into a conjugation map
whose value at a fixed vector is exactly the identity matrix. The two tensor
factors have the same finite coordinate type `m`, the first factor `σ` has an
irreducible rational representation, and no self-duality of `σ` is supplied
or assumed. It works over a field of arbitrary universe `u`. The acting group
is affine for the conjugation-map construction.

`tensorVector M` lists the entries of a rectangular matrix `M : Matrix n m k`
as a vector on `n × m`, row index first. This is the coordinate order of the
existing actual tensor representation `σ.tensor π`.

`intertwines_one` states that the identity matrix intertwines every actual
matrix representation with itself.

`intertwines_dual_of_isFixedVector_tensor` proves that if `tensorVector M` is
an all-test fixed vector of `σ.tensor π`, then `M` intertwines `π.dual` with
`σ`. The proof reads the fixed-vector equation entrywise with the existing
tensor coefficient formula, giving `σ(x) * M * π(x)ᵀ = M` on every affine
test. It then multiplies on the right by the transpose of the inverse of
`π(x)`, which is the actual dual coefficient matrix.

`Intertwines.dual` proves that the transpose of an actual intertwiner from
`ρ` to `σ` intertwines `σ.dual` with `ρ.dual`. `Intertwines.of_mul_eq_one`
proves that a two-sided matrix inverse of an actual intertwiner intertwines
in the opposite direction. Both proofs are matrix identities on every affine
test, using the inverse laws of the general-linear coefficient matrices.

`isUnit_of_intertwines_of_isIrreducible` proves that a nonzero actual
intertwiner `M` from `π` to `σ`, both on `m`, is invertible when the rational
representation of `σ` is irreducible. The proof turns `M` into an
intertwining map of the rational representations with the existing
`Intertwines.rationalMatrix`. Mathlib's
`Representation.IsIrreducible.surjective_or_eq_zero` then makes it
surjective, because it is nonzero. A surjective square matrix is invertible.

`ConjugationLinearMap.ofTensorDualIntertwiner` takes an actual intertwiner
`C` from `ρ` to `σ.tensor π` and an actual intertwiner `D` from `π` to
`σ.dual`. It composes `C` with the Kronecker matrix of the identity and `D`
and applies the existing `ofTensorIntertwiner` adapter. The result satisfies
the unchanged conjugation equivariance equation on every scheme test.
`ofTensorDualIntertwiner_eval` computes the entry `(i, j)` of its value at a
base-field vector `v` as `∑ b, D j b * (C *ᵥ v) (i, b)`.

`ConjugationLinearMap.exists_eval_eq_one_of_tensor` is the main result. Take
an actual intertwiner `C` from `ρ` to `σ.tensor π`, where the rational
representation of `σ` is irreducible. Take an all-test fixed vector `v` of
`ρ` with `C *ᵥ v ≠ 0`. Then some conjugation map from `ρ` to `σ` sends `v` to
the identity matrix. In the proof, `M` is the matrix with
`tensorVector M = C *ᵥ v`. This is a nonzero fixed tensor, so `M` intertwines
`π.dual` with `σ`, and it is invertible by the irreducibility lemma. Its
transpose intertwines `σ.dual` with `π`, using the existing `dual_dual`, so
the inverse `D` of `Mᵀ` intertwines `π` with `σ.dual`. The entry formula for
`ofTensorDualIntertwiner C D` then gives the entries of `M * M⁻¹ = 1`.

The provenance is internal: existing actual tensor and dual coefficient
formulas, the tensor-to-conjugation adapter, the rational-matrix comparison
for intertwiners, and Mathlib's Schur lemma for irreducible representations.
In Mumford–Fogarty–Kirwan, *Geometric Invariant Theory* (3rd ed., 1994),
Appendix 1.A, p. 192, this linear-algebra step is used with an irreducible
self-dual Steinberg module. The adapter here needs neither self-duality nor
any Steinberg data. It constructs no Steinberg or highest-weight
representation, supplies no tensor intertwiner or fixed vector, and does not
by itself prove `SimplyConnectedPositiveCharConjugationMapStatement`.
