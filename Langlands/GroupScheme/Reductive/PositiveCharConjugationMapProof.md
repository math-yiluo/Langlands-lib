# Proof: the simply connected positive-characteristic conjugation map

Author: Worker 4587.

This module proves the published proposition
`Langlands.GroupScheme.SimplyConnectedPositiveCharConjugationMapStatement`
([`PositiveCharConjugationMapStatement`](PositiveCharConjugationMapStatement.md))
at its original universe `u`:

```
theorem simplyConnectedPositiveCharConjugationMap :
    SimplyConnectedPositiveCharConjugationMapStatement.{u}
```

Let `k : Type u` be an algebraically closed field of prime characteristic `p`,
and let `G` be an actual group scheme over `Spec k` with `IsSimplyConnected G`.
Let `ρ` be a matrix representation of `G` on `k^n` for a finite type `n`, and
let `v ≠ 0` be a vector fixed by `ρ` on points over every test scheme. The
theorem gives a positive integer `m`, a representation `σ` of `G` on
`k^(Fin m)`, a `ConjugationLinearMap ρ σ` with coefficient matrix `φ.coeff`, and
a scalar `a ≠ 0` such that the matrix `φ.coeff` evaluated at `v` is `a` times
the identity matrix of size `m`. The theorem adds no hypotheses. The proof does
not change the statement's Lean/Markdown pair or any module that pair imports.

## Implemented proof

The proof is a single term that composes four published theorems:

```
simplyConnectedPositiveCharConjugationMap_of_bigCell
  (steinbergBigCell_of_rootAndCoroot rootDatumExistence
    splitSimplyConnectedCorootSpan)
```

- `simplyConnectedPositiveCharConjugationMap_of_bigCell`, from
  [`SteinbergBigCellReduction`](SteinbergBigCellReduction.md), proves
  `SteinbergBigCellStatement.{u} →
  SimplyConnectedPositiveCharConjugationMapStatement.{u}`. It passes through
  Steinberg covariant exhaustion
  (`steinbergCovariantExhaustion_of_bigCell`), the Steinberg tensor embeddings
  (`steinbergTensorEmbedding_of_covariantExhaustion`) and the published
  conjugation-map construction
  (`simplyConnectedPositiveCharConjugationMap_of_steinberg`).
- `steinbergBigCell_of_rootAndCoroot`, from
  [`SteinbergBigCellRootCorootAssembly`](SteinbergBigCellRootCorootAssembly.md),
  proves `SteinbergBigCellStatement.{u}` from two global inputs:
  `RootDatumExistenceStatement.{u}` and
  `SplitSimplyConnectedCorootSpanStatement.{u}`. It already uses the proved
  dominant highest-weight existence theorem and the proved Steinberg height
  irreducibility theorem, so no further premise remains.
- `rootDatumExistence : RootDatumExistenceStatement.{u}`, from
  [`RootDatumExistence`](RootDatumExistence.md). Every split maximal torus of
  a connected reductive group over a field has a finite reduced root datum
  (Milne, *Algebraic Groups*, Theorem 21.11 and Corollary 21.12).
- `splitSimplyConnectedCorootSpan :
  SplitSimplyConnectedCorootSpanStatement.{u}`, from
  [`SimplyConnected.SplitNecessity`](../SimplyConnected/SplitNecessity.md). For
  an algebraically simply connected group with a split maximal torus and a
  finite reduced root datum of it, the integral coroots span the whole
  cocharacter lattice (Milne, Proposition 23.59, necessity, split case).

All four theorems are stated at the same universe `u` as the target. The
first two are implications, and the last two are unconditional theorems. The
proof therefore needs no instance or universe adjustment.

`lean_check` builds the module with no errors or warnings. The theorem depends
only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The statement is an internal interface extracted from Mumford, Fogarty and
Kirwan, *Geometric Invariant Theory*, third enlarged edition (1994), Appendix
to Chapter 1, Section A, p.192; its paired Markdown records the source. This
module adds no source assertion. Its proof only combines the four published
Library results above, whose own Markdown records their routes and sources.
