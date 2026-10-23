# Evaluation duality on stable images of compact compression

This module proves the entire published proposition
`Langlands.Jacquet.CompactCompressionStableDualityStatement.{uG,uV}` as
`Langlands.Jacquet.compactCompression_stableDuality`. It also exposes
`compactCompression_stableEvaluationDuality`, the existence and evaluation
consequence for fixed representation data, and `compressedAction_adjoint`,
the adjoint identity for the two actual compressed operators.

The group universe `uG` and representation-carrier universe `uV` remain
independent. The group is any topological group, the complex representation
is smooth, `K` is compact open, and `g` is arbitrary. The only finite-dimension
hypothesis concerns the space of `K`-fixed vectors in the original
representation. Zero spaces are allowed. Neither admissibility nor finite
dimension of the ambient representation is assumed.

## Adjointness of the actual compressed actions

Write `X = fixedVectors ρ K.toSubgroup` and
`Y = fixedVectors (smoothContragredient ρ) K.toSubgroup`. The published linear
map `p = smoothDualFixedRestriction ρ K.toSubgroup` is the evaluation pairing
`Y →ₗ[ℂ] Module.Dual ℂ X`. Let `C` be compression by `g⁻¹` on `Y`, and let
`D` be compression by `g` on `X`.

The private lemma `average_eval_constant` says that if a functional is
constant along the compact-subgroup orbit of a vector, evaluating the
normalized average gives its value at that vector. The proof unfolds the
average into the finite orbit mean, applies linearity to the sum, and cancels
the nonzero cardinality of the orbit. The orbit is nonempty even for a zero
vector.

For `ℓ ∈ Y` and `v ∈ X`, the fact that `v` is fixed makes evaluation at `v`
constant on the compact-subgroup orbit of any smooth functional. Thus the
average in `C` can be removed. The contragredient action by `g⁻¹` then gives
`ℓ(ρ(g)v)`. The fact that `ℓ` is fixed makes its evaluation constant on the
compact-subgroup orbit of `ρ(g)v`, so this equals its evaluation on the
average defining `D`. Consequently `compressedAction_adjoint` proves

`p (C ℓ) v = p ℓ (D v)`.

The inverse on the dual side is essential to this calculation. This is an
identity for the published compression and evaluation constructions, without
an assumed abstract adjoint operator.

## The finite-dimensional argument

The two private stable-pairing lemmas work with complex vector spaces `A`
and `B`, a bilinear map `p : A →ₗ[ℂ] Module.Dual ℂ B`, and endomorphisms
`C` and `D` satisfying the displayed adjoint identity. Induction first proves
adjointness for every power.

Suppose both spaces are finite dimensional and `p` is injective. To prove
injectivity of its restriction to the stable images, take `a` in the stable
image of `C` whose pairing with the stable image of `D` vanishes. Choose `n`
such that `range (D^n)` is the stable image of `D`. For every `b`, power
adjointness gives `p (C^n a) b = p a (D^n b) = 0`. Injectivity of `p` implies
`C^n a = 0`. Thus `a` lies both in the supremum of the power kernels of `C`
and in its stable image. Fitting disjointness forces `a = 0`.

The proof uses Mathlib's `LinearMap.eventually_iInf_range_pow_eq` and
`LinearMap.isCompl_iSup_ker_pow_iInf_range_pow` directly. These are also the
Fitting ingredients of the published `CompressionStabilizationProof`; no
additional stabilization premise is introduced.

For bijectivity, assume only that `B` is finite dimensional and that `p` is
bijective. Its injectivity embeds `A` in the finite-dimensional dual of `B`,
so `A` is finite dimensional as well. Surjectivity of `p` makes the flipped
pairing injective. Apply the stable-image injectivity argument to `p, C, D`
and to `p.flip, D, C`. Finally Mathlib's `LinearMap.flip_injective_iff₂`
converts injectivity of the flipped restricted pairing into surjectivity of
the restricted pairing.

## Closing the published statement

The published `Langlands.smoothDualFixedRestriction_bijective` supplies the
bijectivity of the actual pairing `p` on `Y` and `X`. Applying the preceding
argument gives a bijective linear map from the stable image on `Y` to the
full dual of the stable image on `X`.

`LinearEquiv.ofBijective` turns precisely this restricted evaluation map into
the required equivalence. Its evaluation identity is definitional: both
sides evaluate the underlying smooth functional at the underlying vector,
using the published `stableImageToRepresentation` inclusions. The named
consequence `compactCompression_stableEvaluationDuality` asserts this
existence together with evaluation on every pair of stable-image vectors.
The closing theorem introduces all internally quantified data and applies
that consequence, with no extra hypotheses.

## Provenance and scope

This is an internal derived proof from the published compact fixed-vector
duality and the existing finite-dimensional Fitting theory. It does not
attribute this generic formulation or this proof to Casselman. The
historical motivation and its narrower original setting are documented in
the unchanged statement module. No external literature claim is needed for
this implemented argument. It proves no Jacquet quotient, opposite-parabolic
pairing, independence, or equivariance theorem.
