# Joint eigenspace sums and their actual spectral span

Author: Worker 2.

This is an internal construction from the published ordinary joint eigenspaces,
the genuine fixed-space equivalence of a smooth model, and Mathlib's algebraic
direct sum. It makes no new identification with original literature. The actual
tensor specialization uses the existing standard spherical operators on the
entire fixed space of the closed completed tensor slice.

## Ordinary joint spaces and the canonical sum

Let `A` be a complex vector space, let `ι` be an arbitrary index type, and let
`T : ι → Module.End ℂ A`. For each scalar function `c : ι → ℂ`,
`jointEigenspace T c` is the published intersection of the ordinary eigenspaces
of `T i` with eigenvalue `c i`.

`jointEigenspaces_iSupIndep` proves that these submodules form an independent
family. The proof is by finite induction. To separate two distinct scalar
functions `c` and `d`, choose `i` with `c i ≠ d i` and apply
`T i - d i • id`. This kills the `d`-space and preserves every other joint
space: on such a space it acts by its corresponding scalar difference.
The induction hypothesis kills the remaining intersection. Nonzeroness of
`c i - d i` then kills the original vector. Thus the proof needs no
commutation, normality, finite-dimensionality or finite-index assumption.

`jointSpectralSpan T` is the supremum of all these actual submodules.
`jointSpectralSum T` is Mathlib's `DirectSum.coeLinearMap`, from the algebraic
direct sum over all scalar functions to `A`. Its elements have finite support,
and `jointSpectralSum_lof` identifies its value on an inserted summand with that
same original vector. Zero joint spaces are allowed as summands.

`jointSpectralSum_injective` follows from the proved independence using
`iSupIndep.dfinsupp_lsum_injective`. `jointSpectralSum_range` is the actual
range identity supplied by `DirectSum.range_coeLinearMap`.
`jointSpectralSpanEquiv` combines injectivity with that range identity to give
a complex-linear equivalence from the direct sum onto exactly the spectral
span. Its value in `A` is the canonical sum.

`jointSpectralSum_surjective_iff` uses `LinearMap.range_eq_top` and the range
identity to express surjectivity as exactly `jointSpectralSpan T = ⊤`.
Equality with the whole ambient space is an additional obligation.

## Invariance, transport and finiteness

`jointSpectralSpan_map_le` proves that every original `T j` preserves the
span. Mapping the supremum reduces the proof to each joint space, where
`T j x = c j • x` gives membership in the span.

For independently sized complex vector spaces `A` and `B`, a supplied
complex-linear equivalence `e : A ≃ₗ[ℂ] B` that intertwines every `T i` with
`U i` maps each joint eigenspace onto the corresponding joint eigenspace.
`jointSpectralSpan_map_equiv` proves equality of the mapped spectral span
with `jointSpectralSpan U` by mapping the supremum and using the published
joint-space membership equivalence. `jointSpectralSpanTransport` restricts
the same `e` to these spans; its value is `e x`.

`finite_nonzero_jointEigenspaces` assumes only
`FiniteDimensional ℂ A` and applies Mathlib's
`Submodule.finite_ne_bot_of_iSupIndep`. It proves that the set of scalar
functions giving a nonzero joint space is finite even when `ι` is infinite.
This assertion includes the zero space and empty operator family. It does not
assert existence of any nonzero joint space.

The Mathlib implementation used here is pinned by the project environment:
`Mathlib/Algebra/DirectSum/Module.lean` supplies the canonical sum and range,
`Mathlib/LinearAlgebra/DFinsupp.lean` supplies the independence criterion, and
`Mathlib/RingTheory/Noetherian/Basic.lean` supplies finiteness of the nonzero
members of an independent submodule family. The span restriction uses
`LinearEquiv.ofSubmodules` from
`Mathlib/Algebra/Module/Submodule/Equiv.lean`.

## Original corner actions

For a topological group `G` with its Borel measurable structure and Haar
measure `μ`, an open compact subgroup `K`, a representation `τ`, and an
invariant subspace `S`, `cornerSpectralSpan` uses the published original
corner operators on every `K`-fixed vector of `S`.

`factorCornerSpectralSpanEquiv` takes a supplied smooth representation `σ`
and a genuine representation equivalence from `σ` to
`(S ⊓ smoothSubrepresentation τ).toRepresentation`. It applies the span
transport through the published `factorFixedEquiv`; `cornerAction_factor`
proves intertwining for each corner element. In particular, its target is
the full `K`-fixed space of `S`: being fixed by the open subgroup already
implies ambient smoothness. No smoothness of the entire completed action
is required.

`finite_nonzero_cornerJointEigenspaces` assumes actual admissibility of the
same supplied model. `factorFixed_finite` transports its `K`-fixed-space
finiteness to the full fixed space of `S`, and the generic independence result
proves finiteness of the nonzero joint spaces for an arbitrarily indexed
family of corner elements. All measure, subgroup and model inputs remain
explicit. The carrier of the supplied model has an independent universe;
no norm or isometry is required on it.

## Actual completed tensor slices

For an actual number field `F`, a finite tensor presentation `P` of an actual
finite adelic realization, a supplied invariant positive form `b`, a finite
place `v`, and a complementary tensor `y`, the three definitions
`hilbertSphericalSpectralSpan`, `hilbertSphericalSpectralSum`, and
`hilbertSphericalSpectralSpanEquiv` specialize the generic constructions to
`P.sliceHilbertStandardHeckeOperator b v y`.

Their ambient vector space is every spherical fixed vector of the original
closed completed tensor slice, with its inherited Hilbert norm and original
local completed action. The operators retain the canonical integral subgroup,
mass-one spherical Haar measure and standard diagonal double cosets defined in
`Langlands.Representation.Unramified.HeckeOperators`. The scalar index consists
of all functions `Fin (r + 2) → ℂ` for rank `r + 1`. It is not restricted to
normalized scalars arising from a Satake parameter, and no parameter
classification is asserted.

The field and original local-factor universes are independent. These actual
definitions need neither a nonzero-tail premise nor irreducibility or
admissibility. When a genuine original-factor comparison is needed, the existing
`factorHilbertSmoothEquiv` retains its explicit nonzero complementary tensor
and original-factor admissibility assumptions. No concrete finiteness or
original-factor transport wrapper is exported in this module.

These are algebraic sums and equivalences; no direct-sum norm, isometry,
orthogonality, topological closure, spectral density or full-space decomposition
is claimed. The genuine presentation and positive form remain supplied
mathematical data. Their existence, nonzero spectral occurrence and automorphic
occurrence are separate obligations.
