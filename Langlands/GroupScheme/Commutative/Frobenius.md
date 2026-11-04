# Frobenius powers on commutative affine groups

Let `k : Type u` be an arbitrary field, let `p` be its exponential
characteristic, and let `e` be a natural number. For a commutative affine
group scheme `Z` locally of finite type over `Spec k`, the theorem
`CommutativeFrobenius.affinePoints_pow_eq` proves the following identity.
For every commutative `k`-algebra `A : Type u`, every `k`-algebra
endomorphism `g : A →ₐ[k] A` satisfying
`a ^ (p ^ e) = (g a) ^ (p ^ e)` for every `a`, and every affine
`A`-valued point `x` of `Z`,

```text
x ^ (p ^ e) = (g_* x) ^ (p ^ e).
```

No smoothness, connectedness or perfectness hypothesis is used. The identity
is a supporting input for purely inseparable descent of cocharacters.
Quotient unipotence and preservation of maximal tori under field extension
are separate obligations.

The proof first treats matrices over an arbitrary commutative `k`-algebra
`B : Type v`, with a finite matrix index type in `Type`. Assume the two
matrices obtained by applying the tensor inclusions
`B → B ⊗[k] B` to the entries of a matrix `M` commute.
The lemma `coefficient_matrices_commute` applies the tensor product of two
scalar linear functionals to the entrywise commutation equation. This
shows that the resulting scalar coefficient matrices commute.

The definition `coefficientSupport b M` is the finite union of the basis
supports of the entries of `M`, for a `k`-basis `b` of `B`.
The lemma `support_subset_coefficientSupport` proves that it contains each
entry's support. The lemma `matrix_map_eq_sum_coefficients` expresses
every scalar evaluation of `M` as a sum over that finite set. Its summands
are scalar multiples of coefficient matrices. These matrices commute by
the preceding lemma; their scalar multiples also commute.
The lemma `sum_pow_expChar_pow` proves the characteristic-power identity
for a finite commuting family by induction, using Mathlib's two-term
identity. Applying it to the two evaluated expansions proves
`matrix_map_pow_eq`: algebra maps `f, g : B →ₐ[k] A` with
`(f b) ^ (p ^ e) = (g b) ^ (p ^ e)` for all `b` give equal
`p ^ e` powers of the evaluated matrices. The proof handles a trivial
target algebra and an empty matrix index type separately before using
the exponential-characteristic instance on matrices.

For the group theorem, `coeffMatrix_tensor_commute` evaluates a
representation of `Z` at the two universal tensor-valued points.
The points commute because `Z` is commutative. Applying the representation
and the published `TorusUnipotence.affineMatrix_pt` identity gives the
matrix hypothesis above.

Finally, the published `affineLinearEmbeddingStatement` gives a finite
dimensional closed faithful representation of `Z`. Monomorphy reduces
equality of points to equality in that representation. Its coordinate
matrix at `g_* x` is obtained by composing the coordinates of `x` with
`g`, by `Lie.pointCoordinates_naturality`. The matrix power theorem
therefore applies, and injectivity of the faithful representation
gives the asserted equality.

This is an internal derivation from the published affine-coordinate and
linear-embedding constructions and Mathlib's basis, tensor and
characteristic-power identities. It introduces no new structural
assumption about algebraic groups and is not a proof of
`NoTorusUnipotentStatement`.
