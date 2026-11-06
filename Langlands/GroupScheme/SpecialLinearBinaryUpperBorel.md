# The binary upper-triangular special linear Borel subgroup

For every field `k : Type u`, in arbitrary characteristic and universe,
`BinaryUpper.borelRepresentative k` packages the actual inclusion of the
upper-triangular determinant-one binary group into `SL₂` with its proved
`IsBorelSubgroup` property. The underlying group and inclusion are the existing
`BinaryUpper.groupScheme` and `BinaryUpper.inclusion`; no alternate presentation
or assumed structural theorem is supplied.

The elementary obstruction is stronger than maximality of the triangular point
group. Over an infinite field `K`, every solvable subgroup of `GL₂(K)` containing
all upper transvections consists of upper-triangular matrices. If `g₁₀ ≠ 0`,
left multiplication by the upper transvection with coefficient `-g₀₀/g₁₀`
produces `w` with `w₀₀ = 0` and `w₁₀ = g₁₀`. Direct matrix multiplication gives

`w u(s w₀₁ / w₁₀) w⁻¹ = l(s)`.

Thus the subgroup contains both complete opposite root groups. The existing
`GeneralLinear.OppositeRootNonsolvable.not_isSolvable` contradicts solvability:
both roots persist in the derived series. The binary special-linear version
follows by mapping into `GL₂`; entrywise ring-equivalence transport gives the
same conclusion when the coefficient ring is isomorphic to an infinite field.
The elimination itself needs only a field and the indicated nonzero entry;
infinite cardinality is used in the solvability obstruction.

On every relative test scheme over a commutative base ring, the points of the
actual triangular scheme form a solvable abstract group. Their faithful map
into the invertible upper-triangular matrix group reduces this to
`GeneralLinear.UpperTriangularSolvable.isSolvable`. Applying the base-change
point equivalence yields `IsSolvableGroupScheme` over every field.

For maximality, let a smooth solvable group scheme `B'` have a closed inclusion
`i' : B' → SL₂`, and let `f` factor the triangular inclusion through `i'`.
The image of the algebraic-closure point group of `B'` is solvable and contains
every upper transvection, because the corresponding triangular point lifts
along `f`. The canonical `Γ(Spec k̄) ≃ k̄` ring equivalence permits application
of the elementary obstruction. Every such point therefore has lower entry
zero.

Smoothness makes `B'` reduced. The universal lower matrix entry defines a map
to the affine line; the algebraic-closure-point equality theorem for maps from
a reduced scheme over a field shows that this map equals zero. Consequently
the universal point, and by precomposition every relative test point, factors
through the actual triangular inclusion. The represented-subgroup lifting
construction gives an inverse to `f`; the two composite identities follow by
the monomorphism properties of the closed inclusions. This proves maximality
even without using connectedness of the overgroup.

Closedness comes from the existing ideal-cut construction. Smoothness and
connectedness of the triangular group come from
`BinaryUpper.Coordinates.smooth_groupScheme` and
`BinaryUpper.Coordinates.connectedSpace_groupScheme`. Together with solvability
and maximality these supply every field of `IsBorelSubgroup`.

This is an internal construction from explicit binary matrices, the published
opposite-root obstruction, and the universal-point proof method implemented in
`Absolute/GeneralLinearBorelProof`. It proves the Borel property over the ground
field. It does not assert a base-change comparison or parabolicity of this
inclusion, nor classify general local rank-one groups. These comparisons and
the unrestricted `LocalKneserTitsStatement` remain separate obligations.
