# Focused finite-index induction and restriction statements

Worker 312 separates the published proposition
`Langlands.Weil.RepresentationInductionFiniteness.{uG,uV}` in
[`RestrictionInduction`](RestrictionInduction.md) into four standalone
`Prop`-valued definitions. All four names below are in `Langlands.Weil`.
This is an internal decomposition of that derived generic representation-theory
target. It proves none of the four assertions, adds no replacement aggregate,
and changes neither the original aggregate nor its import closure.

## Shared quantifiers and exact conclusions

Every definition universally quantifies, in this order, over
`G : Type uG`, `[Group G]`, `H : Subgroup G`, `[H.FiniteIndex]`,
`V : Type uV`, `[AddCommGroup V]`, `[Module ℂ V]`, and
`[FiniteDimensional ℂ V]`. The universes `uG` and `uV` are independent.
The first three then quantify over `ρ : Representation ℂ H V`;
the fourth instead quantifies over `σ : Representation ℂ G V`.
The definitions have complete unapplied type `Prop`, with all these binders
inside the proposition; they take no proof of a desired conclusion as data.

| Declaration | Conclusion |
| --- | --- |
| `RepresentationInductionDimension` | `FiniteDimensional ℂ (Representation.IndV H.subtype ρ)` and `Module.finrank ℂ (Representation.IndV H.subtype ρ) = H.index * Module.finrank ℂ V`. |
| `RepresentationInductionFiniteImage` | `(Set.range (ρ.ind H.subtype)).Finite ↔ (Set.range ρ).Finite`. |
| `RepresentationInductionSemisimplicity` | `Representation.IsSemisimpleRepresentation (ρ.ind H.subtype) ↔ Representation.IsSemisimpleRepresentation ρ`. |
| `RepresentationFiniteIndexRestrictionSemisimplicity` | `Representation.IsSemisimpleRepresentation (σ.comp H.subtype) ↔ Representation.IsSemisimpleRepresentation σ`. |

The carrier and action are Mathlib's actual `Representation.IndV` and
`Representation.ind`, and restriction is composition with `H.subtype`.
Finite image means finiteness of the whole action's range.
Semisimplicity uses Mathlib's predicate, meaning every invariant subspace has
an invariant complement. The dimension target groups the aggregate's first
two conjuncts; the other rows retain its three remaining clauses.

There is no hypothesis of normality, topology, continuity, finite image, or
finite dimension of the induced carrier. In particular, induced finite
dimension is a conclusion of the first target, not a prerequisite of the
others. Zero-dimensional representations are included: no positive-rank or
nontriviality condition occurs. No irreducibility assertion is made.

## Restriction quantifier check

In the original aggregate the last clause `∀ σ, ...` is inside the preceding
`∀ ρ : Representation ℂ H V` binder, although its formula does not use `ρ`.
For every fixed admissible `G`, `H`, and `V`, that representation type is
inhabited by `Representation.trivial ℂ H V`, which sends every group element
to the identity endomorphism. This exists also for the zero-dimensional
carrier.

Consequently the aggregate implies the standalone restriction target by
specializing `ρ` to this trivial representation and taking its last conjunct.
Conversely, a universally quantified standalone restriction assertion supplies
that last conjunct for every `ρ`. The remaining clauses separate by
conjunction under their common binders. Thus the four standalone targets
together have the same scope as the original aggregate. This explains the
removal of the unused `ρ` binder; it assumes no semisimplicity or finiteness
conclusion. No Lean equivalence theorem or fifth wrapper is added.

## Provenance and source boundary

The immediate mathematical source is the published
`RepresentationInductionFiniteness` and its complete declaration/source map
in `RestrictionInduction.md`. The public
[`Weil statement coverage`](../../../notes/weil/statement-coverage.md)
locates that generic target separately from actual local Weil specialization.

The cited original is John Tate, *Number theoretic background*, in
*Automorphic Forms, Representations and L-Functions*, Proceedings of Symposia
in Pure Mathematics 33, Part II (1979), pages 3–26: section 2.1, printed
pages 9–10 / PDF pages 18–19. Registered literature ID:
`tate-1979-number-theoretic-background`. Retained file:
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
SHA-256: `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
These original pages were read for this decomposition.

On printed page 9 Tate introduces continuous finite-dimensional complex
representations and restriction for Weil groups. On printed page 10 he gives
restriction and induction on virtual representation groups for a finite
separable extension, using the closed finite-index Weil subgroup and usual
Frobenius reciprocity. These pages do not state the four generic targets
verbatim. The existing source map explicitly labels their dimension,
finite-image, and semisimplicity assertions as derived general representation
theory over `ℂ`; the new declarations retain that provenance.

Future proofs may use finite coset coordinates for dimension, a finite coset
action or kernel/core argument for finite image, and normal-core descent,
finite sums of conjugate restrictions, averaging, and identity-coset reflection
for semisimplicity. These are proof directions, not hypotheses, implemented
proofs, or assumptions about unpublished dependencies. Proofs of the components
and their assembly remain separate work.

## Dependencies

The sole direct import is the unchanged published
`Langlands.Weil.Representation.RestrictionInduction`; its existing Mathlib
definitions supply every construction and predicate used here. The approved
environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with Lean 4.34.0 and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
