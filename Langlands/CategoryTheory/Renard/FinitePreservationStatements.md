# Renard A.VIII.1: sequence exactness and finite preservation

Authors: Worker 6 (mathematical specification and shared statement draft),
Worker 595 (direct source and interface checks, compilation and submission).

This statement unit compares Renard's sequence definitions with actual
preservation of finite limits and colimits. The governing original is David
Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, A.VIII.1, printed pages 265–266 / PDF pages 271–272.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`.
The original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both original page extracts were read in full, and PDF272's arrows and
preservation paragraph were checked visually.

The available 2010-edition errata,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were checked on PDF pages 18–19. Their appendix entries correct a later
old argument from "faithful" to "exact"; they do not change these
finite-preservation assertions. The governing 2026 text already uses
"exact" in that later argument. No Renard entry was found in the inspected
Library's project errata notes; this is a bounded observation.

## Source assertions and derived comparisons

Printed page 266 explicitly assumes that the categories are abelian and
the functors additive throughout this discussion. It states that a left
exact functor preserves finite limits and a right exact functor preserves
finite colimits. Those are the forward implications of the first two
equivalences below.

The converse implications are internal comparisons with Mathlib's
finite-preservation interface; they are not attributed as explicit assertions
in that source paragraph. The two-sided equivalence follows by combining
the one-sided comparisons with Renard's definition of exactness as their
conjunction. The aggregate is internal logical packaging of all three
comparisons. These provenance distinctions concern the statements; this
unit contains no proof of any comparison.

The intended reuse route for a subsequent proof is the equivalence between
entries 2 and 4 of each of
`CategoryTheory.Functor.preservesFiniteLimits_tfae F` and
`CategoryTheory.Functor.preservesFiniteColimits_tfae F`, in
`Mathlib/Algebra/Homology/ShortComplex/ExactFunctor.lean`, inspected at
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
That Mathlib file is authored by Joël Riou and Jujian Zhang under Apache 2.0.
Registered source: `mathlib-shortcomplex-exactfunctor-5ed296525643`,
SHA256 `0d767b2a3d4473a0b40ed4b47a220915d0400c9b049931256ff35294b0a50414`.
The cited entries use exactly the source conditions below. The similarly
named convenience wrappers ending in `forall_exact_map_and_mono` and
`forall_exact_map_and_epi` instead display short-exact inputs.

## Full context and actual source predicates

The module is
`Langlands.CategoryTheory.Renard.FinitePreservationStatements`.
All four proposition definitions are in namespace `Langlands.Renard`,
with the complete common context

```lean
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]
```

All four universe parameters are independent. The declarations take the
actual functor and its additivity instance; they do not take an assumed
exactness or preservation comparison. No smallness, concreteness,
module-category, representation, Grothendieck or additional completeness
assumption is imposed.

`Langlands.CategoryTheory.RenardExactFunctor`, authored by Worker 595
with Worker 6's mathematical specification, supplies the already published
source predicates. With the full common context above, they are

```lean
SequenceLeftExact F =
  (∀ S : ShortComplex C,
    S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f))

SequenceRightExact F =
  (∀ S : ShortComplex C,
    S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g))

SequenceExact F = (SequenceLeftExact F ∧ SequenceRightExact F)
```

These displayed equalities explain the imported definitions; they are not
additional declarations in this module. `S.Exact` means exactness at the
middle object of the actual short complex. The left condition also keeps
the first map monic, and the right condition keeps the last map epic.
Neither input is restricted to a short exact sequence. All output
conditions concern the actual `S.map F` and `F.map` arrows.

## Actual finite-preservation predicates

`CategoryTheory.Limits.PreservesFiniteLimits F` is Mathlib's proposition
that `F` preserves limits of every finite small category. For a diagram
`K : J ⥤ C` and a limiting cone on `K`, the mapped cone on `K ⋙ F` is
limiting. The dual predicate
`CategoryTheory.Limits.PreservesFiniteColimits F` takes colimiting cocones
to colimiting cocones. These are universal-property conditions on the
actual functor, not assumptions that some objects of the right shapes
exist or that a selected family of diagrams is preserved.

The classes are defined in
`Mathlib/CategoryTheory/Limits/Preserves/Finite.lean`, authored by Andrew
Yang under Apache 2.0 at the same inspected commit. Registered source:
`mathlib-finite-preservation-5ed296525643`, SHA256
`b1089a0b81f0f9c3ac0ae66c089db0b34c8d60f5fa23a077bd0754588e719cee`.
Their defining fields
range over finite categories in the lowest universe. Mathlib's
`preservesLimitsOfShapeOfPreservesFiniteLimits` and the dual
`preservesColimitsOfShapeOfPreservesFiniteColimits` transport preservation
to every higher-universe finite small shape. Thus no equality between
`u₁`, `u₂`, `v₁`, `v₂` or an indexing universe is required.
Empty and disconnected finite shapes are included. There is no restriction
to nonempty or connected limits or colimits.

## Four exact proposition bodies

With the full common context above and
`open CategoryTheory.Limits`, the declarations are

```lean
def SequenceLeftExactFiniteLimitsStatement : Prop :=
  SequenceLeftExact F ↔ PreservesFiniteLimits F

def SequenceRightExactFiniteColimitsStatement : Prop :=
  SequenceRightExact F ↔ PreservesFiniteColimits F

def SequenceExactFinitePreservationStatement : Prop :=
  SequenceExact F ↔ (PreservesFiniteLimits F ∧ PreservesFiniteColimits F)

def FinitePreservationComparisonStatement : Prop :=
  SequenceLeftExactFiniteLimitsStatement F ∧
    (SequenceRightExactFiniteColimitsStatement F ∧
      SequenceExactFinitePreservationStatement F)
```

Each definition returns `Prop`. The first two retain the source implications
and state the derived converses. The third concerns simultaneous preservation
by the same functor. The fourth groups all three statements with precisely
the displayed conjunction association.

For an actual additive functor `F : Cᵒᵖ ⥤ D`, these general comparisons
can be instantiated with the source category `Cᵒᵖ`. The published
contravariant aliases apply the same source sequence conditions there;
no left/right name interchange is implicit.

## Remaining obligations

The four comparisons remain proposition targets until separately proved.
This statement unit establishes no preservation theorem or global instance.
Preservation of arbitrary exact complexes or homology, reflection of zero
morphisms and faithfulness criteria, Hom left exactness and object-property
dictionaries, smallness, presentations and the module-category equivalence
remain separate obligations of the whole-book program.
