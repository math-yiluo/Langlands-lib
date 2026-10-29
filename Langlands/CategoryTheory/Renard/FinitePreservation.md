# Renard A.VIII.1: proof of the finite-preservation comparisons

Authors: Worker 6 (proof route and Lean proof, from the shared draft of task
`a38c5f8d-65c9-48e8-8437-be85ec8956ce`), Worker 910 (source and target
rechecks, compilation, complete-declaration checks and submission).

This proof unit proves the unchanged published target
`Langlands.Renard.FinitePreservationComparisonStatement F` in
`Langlands.CategoryTheory.Renard.FinitePreservationStatements`, together with
its three named clauses. The module is
`Langlands.CategoryTheory.Renard.FinitePreservation`; all four theorems are in
namespace `Langlands.Renard`.

## Source and provenance

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, A.VIII.1, printed
pages 265–266 / PDF pages 271–272. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Printed page 266 assumes that the categories are abelian and the functors
additive. It states without proof that a left exact functor preserves finite
limits and that a right exact functor preserves finite colimits. Only these
forward implications come from the source. As in the target's Markdown, the
converses, the two-sided comparison and the aggregate are derived
comparisons with Mathlib's preservation predicates. The Lean proof below
does not follow any argument of the source; it reuses Mathlib.

## Reused Mathlib theorems

The proof imports the unchanged target module and Mathlib's
`Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`. That Mathlib file is
authored by Joël Riou and Jujian Zhang under Apache 2.0. It is pinned at
commit `5ed2965256430c3649e86755f9576b54eca72435` and registered as
`mathlib-shortcomplex-exactfunctor-5ed296525643`, SHA256
`0d767b2a3d4473a0b40ed4b47a220915d0400c9b049931256ff35294b0a50414`.
No Mathlib source is copied or edited.

`CategoryTheory.Functor.preservesFiniteLimits_tfae F` is a `List.TFAE` of
four propositions. Its entry 2 (Lean's `TFAE.out` counts from 1) is exactly

```lean
∀ (S : ShortComplex C), S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f)
```

and its entry 4 is `PreservesFiniteLimits F`. In
`CategoryTheory.Functor.preservesFiniteColimits_tfae F`, entry 2 is

```lean
∀ (S : ShortComplex C), S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g)
```

and entry 4 is `PreservesFiniteColimits F`. These entry 2 bodies are
definitionally the published `SequenceLeftExact F` and
`SequenceRightExact F` from `Langlands.CategoryTheory.RenardExactFunctor`.
Neither restricts the input to short exact sequences. Entry 1 of each list
and the convenience wrappers
`preservesFiniteLimits_iff_forall_exact_map_and_mono` and
`preservesFiniteColimits_iff_forall_exact_map_and_epi` use short-exact
input. The proof does not use them.

## The implemented proof

- `sequenceLeftExactFiniteLimits : SequenceLeftExactFiniteLimitsStatement F`
  is `(Functor.preservesFiniteLimits_tfae F).out 2 4`. The target
  `SequenceLeftExact F ↔ PreservesFiniteLimits F` matches this
  equivalence by unfolding `SequenceLeftExact`.
- `sequenceRightExactFiniteColimits : SequenceRightExactFiniteColimitsStatement F`
  is `(Functor.preservesFiniteColimits_tfae F).out 2 4`, in the same way.
- `sequenceExactFinitePreservation : SequenceExactFinitePreservationStatement F`
  applies `and_congr` to the two theorems above. The published
  `SequenceExact F` is by definition
  `SequenceLeftExact F ∧ SequenceRightExact F`, so the result is
  `SequenceExact F ↔ (PreservesFiniteLimits F ∧ PreservesFiniteColimits F)`
  for the same functor `F`.
- `finitePreservationComparison : FinitePreservationComparisonStatement F`
  is the anonymous constructor
  `⟨sequenceLeftExactFiniteLimits F, sequenceRightExactFiniteColimits F,
  sequenceExactFinitePreservation F⟩`. It is right-associated in the same
  way as the target `Left ∧ (Right ∧ Joint)`.

These four theorems are the only declarations in the module. The module
installs no instances.

## Context and scope

The common context, which is identical to the target's, is

```lean
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]
```

Every theorem takes exactly these arguments, in this order, and keeps all
four universes independent. The proof adds no exactness, preservation,
smallness, Grothendieck, module, representation or finite-dimensionality
hypothesis. `PreservesFiniteLimits` and `PreservesFiniteColimits` are
Mathlib's predicates for all finite shapes, so empty and disconnected
diagrams are included.

This unit does not prove that `F` preserves arbitrary exact complexes or
homology, or any faithfulness criterion, Hom left exactness statement or
other part of the book. Those remain separate obligations.
