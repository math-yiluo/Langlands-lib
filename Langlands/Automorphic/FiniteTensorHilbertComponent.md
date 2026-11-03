# Admissible local factors in actual tensor Hilbert slices

Author: Worker 2.

This module constructs intertwiners from a specified local factor and its
positive-form Hilbert completion into the supplied global completion. It
identifies the factor image with the locally smooth part of the actual
completed tensor slice under admissibility, and proves closed irreducibility
of that slice under admissibility and algebraic irreducibility.

## Inputs and actual carriers

The number field `F : Type uF` and local carriers
`V : FinitePlace F → Type uV` have independent universes. Scalars are complex
and the rank `n` is any natural number. The inputs are a
`FiniteTensorPresentation P` of the given family `ρ`, its finite exceptional
set and integral-fixed reference tensors, a positive invariant form `b` on
the actual automorphic realization `S.representation`, a finite place `v`,
and a complementary tensor `y` with explicit `TailNonzero` proof `hy`.
The original carriers `V v` receive no topology.

Write `a = P.factorUnitaryForm b v y hy`. This is the already constructed
form on the given factor `ρ v`, extracted through the actual fixed-tail
slice from the same global form. The source completion is
`a.HilbertCompletion`; the target is `b.HilbertCompletion`.
The target local action is
`b.completedRepresentation.comp (localInclusion F n v).toMonoidHom`,
using the actual finite-completion group and its published topology.
The range is the existing `P.sliceHilbertRange b v y`, with its inherited
subspace topology and action.

## Constructors

`factorHilbertIntertwiner` packages
`P.factorHilbertEmbedding b v y hy` as an intertwiner from
`a.completedRepresentation` to that restricted global completed action.
Its linear map is the existing embedding's linear map. The covariance proof
is linear-map extensionality applied to
`factorHilbertEmbedding_completedOperator`.

`factorHilbertAlgebraicIntertwiner` composes this map with the canonical
`CoefficientHilbertComponentAux.toHilbertIntertwiner a` from `ρ v` to its
completion. Both constructors retain the specified presentation, form,
place, complementary tensor and nonvanishing proof.

## Intrinsic component laws

`sliceHilbertRange_closed_irreducible` assumes `IsAdmissible (ρ v)` and
`Representation.IsIrreducible (ρ v)`. Its conclusion states nontriviality
of the range carrier and that every closed subrepresentation of its
inherited local action is bottom or top. The proof first applies
`CoefficientHilbertComponentAux.completion_closed_irreducible` to `a`,
using the actual group's `compactOpen_cofinal`. It then applies
`closed_irreducible_range` to the existing isometric embedding and its
published range equation. Covariance is obtained from the newly packaged
intertwiner.

`mem_sliceHilbertRange_and_smooth_iff` assumes only
`IsAdmissible (ρ v)`. For every `z : b.HilbertCompletion`, it proves

```text
z lies in the completed slice and is smooth for the inserted local group
  ↔ ∃ x : V v, factorHilbertAlgebraicIntertwiner b v y hy x = z.
```

The proof applies `completion_smooth_recovery` to the actual factor form
and `compactOpen_cofinal`, then transports recovery with
`smooth_range_image`, the same named covariance proof, and
`range_factorHilbertEmbedding_eq_sliceHilbertRange`.

## Provenance and scope

This is internal construction infrastructure derived from the published
actual tensor embedding, invariant range, finite-local compact-open
refinement and coefficient Hilbert component APIs. In particular,
`Langlands/Representation/MatrixCoefficient/HilbertComponentProof`
supplies the completion and range-transfer lemmas; its published proof
is reused by import. No original-literature identification is asserted.

The slice and its smoothness concern the inserted local subgroup.
The construction takes the genuine tensor presentation and global positive
form as inputs; it does not establish their existence, an automorphic
occurrence theorem, or a decomposition of the global Hilbert space.
