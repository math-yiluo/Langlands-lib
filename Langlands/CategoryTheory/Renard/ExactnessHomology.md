# Proof of the sequence-exactness, exact short complex and homology comparisons

Author: Worker 894 (proof implementation, declaration checks and submission).

Module: `Langlands.CategoryTheory.Renard.ExactnessHomology`.
All declarations are in namespace `Langlands.Renard`.

This module proves the published aggregate
`Langlands.Renard.ExactnessHomologyComparisonStatement` of
`Langlands.CategoryTheory.Renard.ExactnessHomologyStatements`. It imports that
statement and the published sequence predicates of
`Langlands.CategoryTheory.RenardExactFunctor` by Lean name and changes neither.
The statement's own Markdown explains the meaning of the three comparisons, the
source definitions and their derived provenance. In short, Renard,
*Représentations des groupes réductifs p-adiques* (French edition dated 9 July
2026), A.VIII.1, printed page 266 / PDF page 272, defines the left and right
sequence conditions for an additive functor between abelian categories. It
states that left exactness preserves finite limits and right exactness preserves
finite colimits. The three equivalences proved here are derived internal
comparisons with Mathlib interfaces. They are not presented as explicit
assertions of Renard's paragraph, and this proof does not follow a proof in the
source.

## Context and closing theorem

The context is the statement's own context:

```lean
open CategoryTheory Limits
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
```

The closing theorem is

```lean
theorem exactnessHomologyComparison (F : C ⥤ D) [F.Additive] :
    ExactnessHomologyComparisonStatement F
```

Its full unapplied type is

```lean
∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive],
  ExactnessHomologyComparisonStatement.{v₁, v₂, u₁, u₂} F
```

with universe parameters `v₁ v₂ u₁ u₂` in that order. The two object universes
and the two Hom universes are independent. The binders are those of the
statement, in the same order: the two implicit categories, their category and
abelian instances, the explicit functor and its additivity instance. No
hypothesis is added. There is no smallness, concreteness, finite-dimensionality,
module, representation or completeness premise beyond the abelian structures.
No finite-preservation, homology-preservation or exactness-comparison premise
is assumed. The axioms used are only `propext`, `Classical.choice` and
`Quot.sound`.

## Declarations

| Declaration | Statement proved |
| --- | --- |
| `sequenceExactShortComplex` | `SequenceExactShortComplexStatement F` |
| `sequenceExactShortExact` | `SequenceExactShortExactStatement F` |
| `sequenceExactHomology` | `SequenceExactHomologyStatement F` |
| `exactnessHomologyComparison` | `ExactnessHomologyComparisonStatement F` |

Each theorem takes `(F : C ⥤ D) [F.Additive]` in the context above. The
aggregate is the anonymous triple
`⟨sequenceExactShortComplex F, sequenceExactShortExact F, sequenceExactHomology F⟩`,
matching the statement's nesting `A ∧ (B ∧ C)`. Each of the three is an
equivalence, so both directions of every comparison are proved.

One step is a `private` theorem used only in this module:

```lean
private theorem sequenceExact_iff_preservesFiniteLimits_and_preservesFiniteColimits
    (F : C ⥤ D) [F.Additive] :
    SequenceExact F ↔ PreservesFiniteLimits F ∧ PreservesFiniteColimits F
```

Its type has the same content as the body of the published
`SequenceExactFinitePreservationStatement F` in
`Langlands.CategoryTheory.Renard.FinitePreservationStatements`. This module
neither imports that statement module nor uses it as an input, and it does not
publish a proof of it or of its aggregate `FinitePreservationComparisonStatement`.
The step is private because those finite-preservation comparisons have their own
task (`e2039435-dc17-46af-b839-614fefcf48aa`) and remain a separate obligation.

## Proof

All Mathlib inputs are in `Mathlib/Algebra/Homology/ShortComplex/ExactFunctor.lean`
at the pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`. Their
category parameters are universe-polymorphic, so they apply with the four
independent universes above. `List.TFAE.out i j` in this Mathlib version uses
one-based indices: it returns the equivalence of the `i`-th and `j`-th entries.

### The private step

`Functor.preservesFiniteLimits_tfae F` is a `List.TFAE` whose second entry is

```lean
∀ (S : ShortComplex C), S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f)
```

and whose fourth entry is `PreservesFiniteLimits F`. The second entry is,
literally, the body of the published definition `SequenceLeftExact F`. So
`(Functor.preservesFiniteLimits_tfae F).out 2 4` is
`SequenceLeftExact F ↔ PreservesFiniteLimits F`, after unfolding that
definition.

In the same way, the second entry of `Functor.preservesFiniteColimits_tfae F` is
the body of `SequenceRightExact F`, with `Epi S.g` and `Epi (F.map S.g)`, and
its fourth entry is `PreservesFiniteColimits F`. So `.out 2 4` gives
`SequenceRightExact F ↔ PreservesFiniteColimits F`.

`SequenceExact F` is by definition `SequenceLeftExact F ∧ SequenceRightExact F`.
`and_congr` combines the two equivalences into the private step. No rewriting
is used; Lean checks the match by unfolding the published definitions.

### The three comparisons

`Functor.exact_tfae F` is a `List.TFAE` with entries

1. `∀ (S : ShortComplex C), S.ShortExact → (S.map F).ShortExact`;
2. `∀ (S : ShortComplex C), S.Exact → (S.map F).Exact`;
3. `PreservesHomology F`, which is `F.PreservesHomology`;
4. `PreservesFiniteLimits F ∧ PreservesFiniteColimits F`.

Each comparison composes the private step with one equivalence from this list
by `Iff.trans`:

- `sequenceExactShortComplex` uses `.out 4 2`. Its right side is preservation
  of every middle-exact short complex, which is the body of
  `SequenceExactShortComplexStatement F`.
- `sequenceExactShortExact` uses `.out 4 1`. Its right side is preservation of
  every actual short exact complex, with all three fields of `ShortExact` in the
  conclusion. This is the body of `SequenceExactShortExactStatement F`.
- `sequenceExactHomology` uses `.out 4 3`. Its right side is Mathlib's actual
  class `F.PreservesHomology`, which is the body of
  `SequenceExactHomologyStatement F`.

In both the statement and the Mathlib entries, `S.map F` uses the
`F.PreservesZeroMorphisms` instance supplied by `[F.Additive]`.

## Checks

The module compiles in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean `v4.34.0`) with no errors or
warnings. A separate private check printed the full unapplied types of
`exactnessHomologyComparison` and `ExactnessHomologyComparisonStatement` with
universes and explicit instances. It also elaborated the closing theorem
against the full type displayed above and against the unfolded conjunction of
the three equivalences. That check is not part of this submission.

## Scope

This module closes only the proof of the aggregate. It builds no chain-complex
functor and no natural homology comparison isomorphism. The proofs of the
finite-preservation comparison statements, the faithfulness statements, the Hom
object-property work and the rest of the book remain separate obligations.
The direct route through the three Mathlib `TFAE` lemmas was identified in the
statement unit's interface audit by Worker 6 and Worker 691; this module
implements it.
