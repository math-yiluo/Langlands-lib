# Hyperbolic splitting and rank-one Hermitian coordinates

Author: Worker 176.

This module constructs linear coordinates for a nondegenerate Hermitian space
with a nonzero isotropic vector. Under the additional bound that every actual
totally isotropic submodule has dimension at most one, the middle space is
anisotropic and admits diagonal coordinates. The coefficient fields have a
common arbitrary universe; the vector space may lie in a different universe.
There is no characteristic restriction.

The main constructions are `HermitianRoot.hyperbolicMiddle`,
`hyperbolicProjection`, `hyperbolicCoordinates` and `negativeMiddlePairing`.
Their intrinsic lemmas culminate in `exists_rankOne_diagonal_coordinates`.
This is a linear-algebra component of Task 5813, not a proof of
`OuterTypeARankOneHermitianStatement`. The module does not construct a quadratic
extension from an index or identify an arbitrary group scheme with a unitary
model.

The pairing `h` is linear in its first variable and conjugate-linear in its
second, with involution `SU3Root.fieldInvolution K L` for a separable quadratic
extension `L/K`. Hermitian symmetry is an explicit hypothesis. The first
lemma, `exists_hyperbolic_partner`, assumes nondegeneracy and a nonzero
isotropic vector `x`. Nondegeneracy supplies a vector with nonzero pairing
against `x`. Rescaling it gives a vector `z` with both cross pairings one.
The proof then sets `a = SU3Root.traceOne K L * h z z` and takes `y = z - a • x`.
The sum of `a` with its conjugate is `h z z`, so `y` is isotropic and retains
both cross pairings one. This uses the published trace-one element and never
divides by two, including in characteristic 2.

For a chosen pair `x,y` with zero self-pairings and cross pairings one,
`hyperbolicMiddle h x y` is the intersection of the kernels of `v ↦ h v x` and
`v ↦ h v y`. The explicit linear projection is
`v ↦ v - h v y • x - h v x • y`. The linear equivalence
`hyperbolicCoordinates` sends `v` to `(h v y, projection v, h v x)` in
`L × (hyperbolicMiddle h x y × L)`. Its inverse sends `(a,z,b)` to
`a • x + z + b • y`.

`hyperbolicCoordinates_symm_pairing` and `hyperbolicCoordinates_pairing` prove
that the full pairing in these coordinates is
`a * bar b' + h z z' + b * bar a'`. Hermitian symmetry makes the middle
orthogonal to the two hyperbolic vectors in both variables. In finite
dimension, `hyperbolicMiddle_finrank` proves that the dimension decreases by
two.

`hyperbolicMiddle_isAnisotropic` assumes that for each submodule `W`, vanishing
of `h` on every pair of elements of `W` implies `finrank L W ≤ 1`. If a
nonzero isotropic middle vector existed, it and `x` would span a totally
isotropic plane. The proof realizes this plane as the range of an injective
linear map `L × L →ₗ[L] V`, computes its dimension as two, and contradicts the
bound. Only the zero self-pairing of `x` and its pairing one with `y` are
needed for this argument, in addition to Hermitian symmetry and the middle
membership conditions.

The Library's `HermitianRoot.gram H` uses the negative of the diagonal middle
form. Accordingly `negativeMiddlePairing` is the negative of the restriction
of `h` to the actual middle submodule. Its symmetry and anisotropy lemmas allow
application of the published `exists_anisotropic_diagonal_coordinates`.
`exists_rankOne_diagonal_coordinates` assembles the constructions: if
`finrank L V = m + 2`, it produces an anisotropic diagonal form `H` on `Fin m`
and an `L`-linear equivalence `e : V ≃ₗ[L] L × ((Fin m → L) × L)` such that

```
h v w = (e v).1 * bar (e w).2.2
        - H.pairing (e v).2.1 (e w).2.1
        + (e v).2.2 * bar (e w).1.
```

This module is an internal elementary derivation. Its ingredients are linear
and semilinear map operations, finite-dimensional submodule arguments, the
published quadratic-extension trace-one element, and the published
anisotropic Hermitian diagonalization theorem. It does not transcribe or
assert an external classification theorem. Relating a general matrix form's
Witt index to the submodule bound, transporting these coordinates into matrix
congruences, and constructing the all-test presentation of the given group
remain separate obligations.
