# Renard A.VIII.1: faithfulness and reflection of zeros

Authors: Worker 6 (mathematical specification and shared statement draft),
Worker 633 (direct source verification, declaration inspection and submission).

This statement unit records two faithfulness criteria from David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, A.VIII.1, printed page 266 / PDF page 272. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`. The original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original page was reread directly and the source fingerprint and
296-page count verified on 26 October 2026 by Worker 6. Worker 633 reread
and visually checked PDF272 and independently verified the same source
fingerprint and page count on 28 October 2026.

The available 2010-edition errata,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were reread in full on PDF pages 18–19 by Worker 6 on 26 October 2026
and Worker 633 on 28 October 2026. The old printed-page-308 argument
is corrected from faithfulness to exactness when asserting preservation
of epimorphisms and monomorphisms. The governing 2026 paragraph already
uses exactness. The following erratum about sufficiency concerns the
subsequent Hom argument. No project `notes/errata` directory was present
in the workspace or its startup Library base; this is a bounded observation.

## Source assertions and derived content

The beginning of printed page 266 explicitly assumes abelian categories
and additive functors throughout the discussion. The faithfulness
paragraph recalls injectivity of the actual Hom maps and asserts that
reflection of zero morphisms suffices for faithfulness. This is the
right-to-left implication of `FaithfulZeroMorphismCriterionStatement`.
The left-to-right implication is the elementary derived necessity
comparison, included to expose an equivalence. The paragraph does not
explicitly present that equivalence.

The unnumbered lemma immediately before A.VIII.2 asserts that an exact
functor which reflects zero objects is faithful. This is
`SequenceExactReflectsZeroFaithfulStatement`. The source motivates it
using the epi/mono image factorization: exactness preserves its two
arrows, and a zero mapped morphism has zero image. That explanation
introduces no additional premise into our statement.

`FaithfulnessCriteriaStatement` is an internal conjunction of these two
propositions. The converse in the first criterion and this conjunction
have derived provenance. This module contains statement definitions;
neither criterion is proved here.

## Complete context and proposition bodies

The module is
`Langlands.CategoryTheory.Renard.FaithfulnessStatements`.
All three definitions lie in namespace `Langlands.Renard`. Their full
common category context is

```lean
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
```

All four universe parameters are independent. With
`open CategoryTheory` and `open CategoryTheory.Limits`, the complete
definition signatures and bodies under this context are

```lean
def FaithfulZeroMorphismCriterionStatement (F : C ⥤ D) [F.Additive] : Prop :=
  F.Faithful ↔
    (∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f = 0 → f = 0)

def SequenceExactReflectsZeroFaithfulStatement
    (F : C ⥤ D) [F.Additive] : Prop :=
  SequenceExact F →
    (∀ X : C, IsZero (F.obj X) → IsZero X) →
      F.Faithful

def FaithfulnessCriteriaStatement (F : C ⥤ D) [F.Additive] : Prop :=
  FaithfulZeroMorphismCriterionStatement F ∧
    SequenceExactReflectsZeroFaithfulStatement F
```

Each definition returns `Prop` and explicitly retains the actual functor
and its additivity instance. In particular, the first body's elaboration
does not need additivity, so merely declaring a section variable
`[F.Additive]` would allow Lean to omit it. The explicit binder preserves
the stated source context. The first criterion has a preadditive
generalization, but this unit retains the common abelian scope.

There are no smallness, concreteness, module-category, representation,
finite-dimensionality or additional completeness assumptions.
Exactness and reflection are antecedents of the second proposition,
rather than parameters certifying its conclusion. Its reflection
antecedent quantifies every `X : C`.

## Actual categorical interfaces

`CategoryTheory.Functor.Faithful F` is Mathlib's proposition that the
actual map

```lean
F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)
```

is injective for every pair `X Y : C`. The class and its
`map_injective` field are in
`Mathlib/CategoryTheory/Functor/FullyFaithful.lean`. The zero-morphism
condition in the first proposition quantifies the actual arrows of `C`
and uses the categorical zero arrows supplied by the abelian structures.
It does not substitute a different faithful representation of a Hom group.
Additivity is Mathlib's existing `F.Additive` on these same maps.

`CategoryTheory.Limits.IsZero X`, defined in
`Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean`, means there is a
unique arrow from `X` to each object and a unique arrow from each object
to `X`. Thus the second premise expresses that whenever `F.obj X` is a
zero object, `X` is also a zero object. It is invariant under isomorphism
and imposes no equality with a chosen zero object. In an abelian category
this is the categorical meaning of the source's notation that an object
is zero.

The imported `Langlands.CategoryTheory.RenardExactFunctor`, authored by
Worker 595 with Worker 6's mathematical specification, supplies the
already published source predicates. With the common context above,

```lean
SequenceExact F = (SequenceLeftExact F ∧ SequenceRightExact F)

SequenceLeftExact F =
  (∀ S : ShortComplex C,
    S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f))

SequenceRightExact F =
  (∀ S : ShortComplex C,
    S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g))
```

These are explanatory unfoldings of imported definitions. Neither
one-sided condition restricts its inputs to short exact sequences.
The second faithfulness criterion uses precisely this source exactness,
without adding a finite-preservation comparison as a premise.

## Proof and program boundaries

At inspected Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`,
`Functor.zero_of_map_zero` and `Functor.map_eq_zero_iff` in
`CategoryTheory/Limits/Preserves/Shapes/Zero.lean` are useful for the
necessary direction. `Functor.mapAddHom` and `Functor.map_sub` in
`CategoryTheory/Preadditive/AdditiveFunctor.lean` provide a route for
the sufficient zero-morphism criterion. These are navigation for
subsequent proof work, rather than proofs in this unit. The actual
abelian image-factorization route for the exact zero-object criterion
remains a separate proof obligation.

No faithful instance or faithfulness theorem is installed here. Finite
preservation, preservation of arbitrary exact complexes or homology,
Hom object-property dictionaries, smallness, presentations and
categorical equivalence remain separate whole-book obligations.
