# Pseudo-complete schemes over an arbitrary field

Worker 1333 implemented this module using the interface design of Worker 1305
and the scope coordinated by Worker 1293.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), Definition C.1.1, printed p.581, one-based PDF p.607. Its registered
source ID is `conrad-gabber-prasad-2015-pseudo-reductive`, with SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

## Mathematical interface

For every `k : Type u` with `[Field k]`, `Langlands.GroupScheme.IsPseudoComplete X`
is a proposition about an actual relative scheme
`X : Over (Spec (CommRingCat.of k))`. It has four fields:

- `isSeparated : IsSeparated X.hom`;
- `locallyOfFiniteType : LocallyOfFiniteType X.hom`;
- `quasiCompact : QuasiCompact X.hom`;
- `dvrLifting : PseudoComplete.HasDVRLifting X`.

The middle two fields together express finite type. For every `k`-algebra
`R : Type u` that is an integral domain and a discrete valuation ring, the
last field requires an extension of every relative fraction-field point
`x : Spec (FractionRing R) → X`, provided that the residue extension over
`k` is generally separable. The extension `xR : Spec R → X` must satisfy
`PseudoComplete.genericPoint R ≫ xR = x` in the relative category.

This is the existence part of the source's equality `X(R) = X(K)`.
Separatedness supplies uniqueness in the mathematical definition. This
module does not separately formalize the uniqueness consequence.
`FractionRing R` is Mathlib's canonical fraction field; an adapter for an
arbitrary separately supplied fraction-field model is not part of this module.

## Canonical algebra structures and size

`PseudoComplete.algebraSpec k A` abbreviates the actual `algSpec` object for
the supplied `k`-algebra `A`. Its structure map is the spectrum map of
`algebraMap k A`, as recorded by `algebraSpec_hom`.
The existing localization instances give `FractionRing R` its induced
`k`-algebra structure through `R`. The morphism `genericPoint R` is the
relative spectrum of `IsScalarTower.toAlgHom k R (FractionRing R)`;
`genericPoint_left` identifies its underlying scheme morphism with the
spectrum map of `algebraMap R (FractionRing R)`.
The residue field likewise has its induced `k`-algebra structure via the
canonical residue map from `R`.

The lifting quantifier explicitly tests **every** DVR `R : Type u`, in the
same universe as `k` and the geometry. It does not test rings in a larger
universe. There is no characteristic restriction. No reduction to
power-series rings is made: using the alternate criterion of CGP Remark
C.1.4 would require its equivalence proof.

## General separability

The residue condition is
`Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField R)`.
For fields this is the geometric-reducedness characterization of general
separability and permits transcendental extensions. In contrast,
`Algebra.IsSeparable k F` requires every element to be algebraic and separable,
so it would restrict the DVR tests incorrectly.

The imported Mathlib predicate is compared with reducedness of
`AlgebraicClosure k ⊗[k] F` by
`Algebra.isGeometricallyReduced_field_iff`. This module uses that existing
predicate directly; it adds no theorem about arbitrary tensor base changes.

## Basic laws and boundaries

The structure projections expose each hypothesis and `IsPseudoComplete.mk`
constructs the predicate. `isPseudoComplete_iff` packages all four clauses as
a conjunction. `IsPseudoComplete.finiteType` extracts the two finiteness
fields, and `IsPseudoComplete.exists_extension` applies the valuative
clause with its relative restriction equation. Their proofs are the direct
structure constructor and projections.

The relative spectrum helpers and these basic laws are internal formal
packaging of Definition C.1.1. The definition assumes no fixed-point
existence, quotient completeness or properness, radical existence, or
conjugacy conclusion.
