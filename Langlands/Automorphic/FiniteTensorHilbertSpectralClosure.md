# Closed joint spectral subspaces and actual tensor slices

Author: Worker 2.

This internal construction takes the closure of the supremum of the published
ordinary joint eigenspaces of the original bounded operators. It introduces no
new identification with the original literature. The intrinsic laws use
Mathlib's topological submodule closure, continuous restriction, closed kernels
and orthogonal projection. The final definitions apply them to the original
standard spherical operators of an actual completed tensor slice.

## The closed subspace and its original operators

Let `H` be a complex normed space, let `ι` be any type, and let
`T : ι → H →L[ℂ] H`. The existing `jointEigenspace` is the intersection of
ordinary eigenspaces, so membership in its `c`-space means
`T i x = c i • x` for every `i`.

`TensorHilbertHeckeAux.jointSpectralClosure T` is the topological closure of the
submodule supremum of these spaces over all functions `c : ι → ℂ`.
The supremum is the algebraic span: each of its elements is a finite sum of
original common eigenvectors. The closure uses the original norm topology.
`jointSpectralClosure_isClosed` proves closedness, and
`jointEigenspace_le_jointSpectralClosure` includes every original ordinary joint
space. There is no restriction to normalized Satake scalar systems.

`jointSpectralClosure_map_le` proves invariance under each original `T j`.
On each joint space, `T j` is scalar multiplication and hence preserves the
algebraic span. Mathlib's `Submodule.topologicalClosure_map` and monotonicity of
closure then prove invariance of its closure. This argument requires no
commutation of the ambient operators.

`jointSpectralClosureAction T i` restricts `T i` to this invariant closed
submodule as a continuous linear endomorphism. Its norm is the inherited
subspace norm. `jointSpectralClosureAction_apply_val` states that its value in
`H` is exactly `T i x`.

`jointSpectralClosure_le_commutator_ker` proves that this closed submodule lies
in the kernel of `(T i).comp (T j) - (T j).comp (T i)`. On a joint eigenvector
both compositions have the same product of complex scalars. The commutator is
continuous, so its closed kernel contains the closure of the algebraic span.
`jointSpectralClosureAction_commute` consequently proves that the original
restricted operators commute on the closed subspace. This does not assert that
the original operators commute on all of `H`.

## Continuous transport, finite dimension and density

For an independently sized complex normed space `J`,
`jointSpectralClosure_map_equiv` assumes an actual continuous complex-linear
equivalence `e : H ≃L[ℂ] J` intertwining every `T i` with a supplied bounded
operator `U i`. The published ordinary-eigenspace comparison identifies each
pair of joint spaces with the same scalar function. Mapping suprema identifies
their algebraic spans, and `ContinuousLinearEquiv.image_closure` identifies
their closures. The conclusion is exact equality of the mapped submodules.

`jointSpectralClosureTransport` restricts this same `e` using
`ContinuousLinearEquiv.ofSubmodules`. Its value law is the original `e x`.
An arbitrary algebraic smooth-model equivalence is insufficient for this
closure-transport statement; no continuity or isometry of such a model is
inferred here.

Under `FiniteDimensional ℂ H`, `jointSpectralClosure_eq_iSup` proves that the
algebraic supremum is already closed. It uses Mathlib's closedness of
finite-dimensional submodules. This does not make that supremum equal to `H`.

`jointSpectralClosure_eq_top_iff` states the exact remaining condition:
the closed submodule is top if and only if the original algebraic span is
dense in `H`. Neither density nor diagonalizability is supplied. The index type
can be infinite or empty, and the carrier can be zero throughout this generic
construction.

## Orthogonal projection

For a complete complex inner-product space `X`, the proved closedness supplies
completeness of `jointSpectralClosure T` with its inherited norm.
`jointSpectralClosureProjection T` is the orthogonal projection onto this
submodule, as a continuous linear endomorphism of the entire original `X`.
It uses Mathlib's `Submodule.starProjection`.

The range is exactly `jointSpectralClosure T`; the kernel is its orthogonal
complement. The projection fixes a vector exactly when it belongs to the closed
submodule. It is idempotent and symmetric, its operator norm is at most one,
and the residual `x - jointSpectralClosureProjection T x` lies in that orthogonal
complement. These laws use the corresponding proved `starProjection` laws.

`jointSpectralClosureProjection_eq_id_iff` identifies equality with the identity
operator with the condition that the closed submodule is top. In the forward
direction it compares the actual ranges. In the reverse direction the
fixed-vector criterion gives equality at each vector. Together with the density
criterion above, this leaves full-space spectral density as an explicit
additional obligation.

No claim is made that this projection commutes with the original ambient
operators, or that those operators preserve the orthogonal complement. Neither
claim follows from the invariance proved here without further hypotheses.

## Actual completed tensor slices

The actual definitions retain independent universes for the number field and
the original local-factor carriers. Coefficients are complex and the rank is
`r + 1`. The inputs are a genuine `FiniteTensorPresentation P` into an actual
finite automorphic realization and an invariant positive form `b` on that
realization.

For every finite place `v` and complementary tensor `y`,
`P.hilbertSphericalSpectralClosure b v y` is the preceding closed submodule
inside `P.SliceHilbertSphericalVectors b v y`. That carrier is the entire
spherical fixed space of `P.sliceHilbertRange b v y`, the actual closed
invariant slice in the global Hilbert completion.
The family is exactly `P.sliceHilbertStandardContinuousHeckeOperator b v y`,
indexed by `Fin (r + 2)`. Forgetting continuity recovers the published
`sliceHilbertStandardHeckeOperator`, so the closure concerns the original
algebraic eigen-equations.

`P.hilbertSphericalSpectralClosureAction b v y i` is the generic restriction of
the same bounded standard operator to this actual closed spectral subspace.
The generic invariance, value and commutation laws apply to this family.

`P.hilbertSphericalSpectralClosureProjection b v y` is the generic orthogonal
projection on the entire actual spherical fixed space. Its needed completeness
is proved using `fullFixed_completeSpace`: the actual slice is closed in the
complete global Hilbert space, and every original local group operator
preserves its norm by `b.completedRepresentation_norm` at `localInclusion`.
The subgroup is exactly the canonical `Correspondence.sphericalSubgroup`.
Thus completeness is proved for all these fixed vectors, without assuming that
the entire completed local representation is smooth.

The published standard operators use the same canonical integral subgroup,
mass-one spherical Haar measure and standard diagonal double cosets. This
construction changes none of those normalizations and uses the inherited
global Hilbert norm. The three actual constructors are exported; separate
concrete wrappers for all generic laws are not exported.

Zero complementary tensors are allowed. No nonzero-tail, irreducibility or
admissibility premise is used by these actual definitions. Recovering an
original local-factor model elsewhere still retains its nonzero-tail and
admissibility inputs, and that algebraic recovery alone does not supply
continuous transport of this closure.

This unit does not construct the supplied presentation or positive form and
asserts no nonempty spectrum, normality, pairwise orthogonality of distinct
joint spaces, Hilbert direct-sum decomposition, spectral density,
classification or automorphic occurrence. It supplies the actual closed
subspace, its inherited bounded action and its orthogonal projection, with
their intrinsic generic laws.
