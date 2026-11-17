# Averaging projections into actual stable subspaces

For a field `k`, an affine group scheme `G` over `k`, a finite coordinate matrix
representation `ρ`, and a normalized all-algebra invariant coordinate integral
`I`, `averagedMatrix ρ I P` averages the universal conjugates of the linear
endomorphism matrix `P`. The theorem `averagedMatrix_intertwines` proves that it
commutes with the actual representation on every commutative `k`-algebra.

The theorem `IsStableSubspace.exists_stable_complement` states that every actual
stable subspace `W` of this representation has a stable subspace `U` with
`IsCompl W U`. No characteristic, smoothness, connectedness or finite-type
hypothesis is used; the invariant integral is an explicit input.

## Construction and proof

`integralMatrix` abbreviates the existing affine representation matrix.
`conjugateMatrix ρ P x` is `ρ(x) P ρ(x⁻¹)`, with the ground-field matrix extended
to the coefficient algebra. Its naturality follows from that of the existing
representation. `integralUniversalPoint` is the point corresponding to the
identity algebra map of the chosen coordinate algebra, and `averagedMatrix`
applies `I.linearForm` to every entry of its conjugate matrix.

`averagedMatrix_baseChange` identifies the scalar extension of this matrix with
the contraction of the same universal conjugates over any coefficient algebra.
The two `contract_matrix_mul` lemmas move constant matrix factors through this
contraction. Left translation of the universal variable conjugates its matrix
by the constant point. The all-algebra left-invariance of `I` therefore makes
the average commute with that point, proving `averagedMatrix_intertwines`.

For a matrix `P` whose columns lie in a stable subspace `W` and whose action on
`W` is the identity, `IsStableSubspace.projection_matrix` uses separation by
linear functionals to prove `P ρ(x) P = ρ(x) P` over every test algebra. Applying
this at the universal point and its inverse shows, for the universal conjugate
`Q(x)`, that `P Q(x) = Q(x)` and `Q(x) P = P`. Entrywise integration preserves
both identities; the second uses `I.linearForm 1 = 1`. This is
`averagedMatrix_projection`.

To construct the complement, take published finite split coordinates `B, C`
for `W` and use `P = B C`. The averaged matrix has image in `W` and fixes `W`.
Its kernel is stable by its intertwining property. The standard linear
projection lemma then proves that this kernel complements `W`.

## Provenance

This is a derived internal construction from the Library's
`CoordinateIntegration.InvariantIntegral` and its tensor contraction API,
the existing all-affine-tests `IsStableSubspace`, finite split coordinates,
and Mathlib's `LinearMap.isCompl_of_proj`. The mathematical purpose is the
stable-complement criterion discussed after Proposition 4.17 in James S. Milne,
*Algebraic Groups* (2017), printed p.90 (PDF p.106), registered source
`milne-2017-algebraic-groups`. Milne's Definition 4.15 supplies the semisimplicity
convention for the later application; this module itself does not state that
application. The 2017 and 2022 author errata snapshots were checked; neither
changes this criterion. The proof here is the invariant-integral averaging
route and does not assert that Milne's proof of Theorem 22.42 uses that route.
