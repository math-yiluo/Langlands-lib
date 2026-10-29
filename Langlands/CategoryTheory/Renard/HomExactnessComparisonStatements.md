# Renard A.VIII.2: Hom left exactness and lifting comparisons

Authors: Worker 6 (source reading, statements and documentation),
Worker 923 (independent source, errata and Mathlib checks, the opposite
category reading below, declaration inspection and submission).

This statement unit covers the two Hom left-exactness assertions in David
Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, A.VIII.2, printed page 267 / PDF page 273. It also states
the derived comparisons between Renard's definitions of projectivity and
injectivity and Mathlib's lifting classes. Those comparisons are internal
source-to-Mathlib identifications, not separately numbered source results.

The governing registered source is
`renard-2026-representations-groupes-reductifs-padiques`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The full text of PDF pages 272–273 and the image of PDF273 were read.
A.VIII.1, printed page 266 / PDF page 272, supplies the additivity and
opposite-category exactness conventions.

The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was reread at its appendix entries on PDF pages 18–19. These correct an
old use of faithfulness to exactness, the direction of the nonzero-Hom
criterion argument and the object in the smallness definition. They do
not change the Hom left-exactness assertions or projective/injective
definitions used here. The 2026 text governs.

## Context and actual constructions

All five declarations belong to namespace `Langlands.Renard` in module
`Langlands.CategoryTheory.Renard.HomExactnessComparisonStatements`.
Their complete common context is

```lean
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
```

Each declaration takes `(P : C)` and returns `Prop`. The object universe
`u` and Hom universe `v` remain independent. The category is arbitrary
abelian; there are no smallness, concreteness, cocompleteness,
Grothendieck, enough-projectives or enough-injectives assumptions.

The imported `HomFunctors` pair, authored by Worker 734 from Worker 6's
specification, constructs the actual functors

```lean
Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P :
  C ⥤ ModuleCat.{v} ℤ

Langlands.CategoryTheory.Renard.preadditiveYonedaInt P :
  Cᵒᵖ ⥤ ModuleCat.{v} ℤ
```

Their carriers are `P ⟶ X` and `X ⟶ P`, with their canonical integer
module structures. For `g : X ⟶ Y` their maps are respectively
`f ↦ f ≫ g` and, on `g.op`, `h ↦ g ≫ h`. This uses the well-typed
composition convention explained in the imported pair's discussion of
the source's arrow labels. Both functors are additive.

The imported `RenardExactFunctor` pair, authored by Worker 595 with
Worker 6's specification, defines the source's one-sided sequence
conditions. The imported `HomObjectProperties` pair, authored by
Worker 6 and Worker 595, defines `HomProjective` and `HomInjective` by
two-sided exactness of these same functors. These constructions and their
intrinsic laws are reused unchanged. This unit introduces no substitute
functors or new object-property definitions.

## Exact statements

The first two declarations are

```lean
def CovariantHomLeftExactStatement (P : C) : Prop :=
  SequenceLeftExact
    (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P)

def ContravariantHomLeftExactStatement (P : C) : Prop :=
  ContravariantSequenceLeftExact
    (Langlands.CategoryTheory.Renard.preadditiveYonedaInt P)
```

They express the explicit source assertion that both Hom functors are
left exact. For the covariant functor `F`, the first body expands to

```lean
∀ S : ShortComplex C,
  S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f)
```

For the contravariant functor `G : Cᵒᵖ ⥤ ModuleCat.{v} ℤ`, the second
has exactly the same expression with `S : ShortComplex Cᵒᵖ` and `G`
in place of `F`. This is the published convention: a contravariant
functor is treated as a covariant functor on the opposite category,
without swapping the names of the one-sided conditions. Read in `C`,
an input `S : ShortComplex Cᵒᵖ` is Mathlib's `S.unop`, the composable
pair `S.g.unop : S.X₃.unop ⟶ S.X₂.unop` and
`S.f.unop : S.X₂.unop ⟶ S.X₁.unop`. `Mono S.f` in `Cᵒᵖ` says that
`S.f.unop` is an epimorphism in `C`, and Mathlib's
`ShortComplex.exact_unop_iff` identifies exactness of `S.unop` with
exactness of `S`. So the tested inputs are exactly the exact sequences
`Z ⟶ Y ⟶ X ⟶ 0` in `C`, and the conclusion says that
`0 ⟶ Hom(X, P) ⟶ Hom(Y, P) ⟶ Hom(Z, P)` is exact, the first map being
injective. This reading is explanatory; the Lean body is the published
`Cᵒᵖ` predicate itself, not a restatement through `unop`. In both cases
all exact inputs with the specified initial monomorphism are tested;
the final arrow need not be an epimorphism. The statements do not replace
these inputs by short exact sequences or by finite-limit preservation.

The derived comparisons are

```lean
def HomProjectiveComparisonStatement (P : C) : Prop :=
  HomProjective P ↔ CategoryTheory.Projective P

def HomInjectiveComparisonStatement (P : C) : Prop :=
  HomInjective P ↔ CategoryTheory.Injective P
```

On each left-hand side, Renard's definition requires both published
one-sided sequence conditions on the actual Hom functor. The imported
contravariant two-sided condition is `SequenceExact` on `Cᵒᵖ`.

The right-hand sides are Mathlib's actual lifting and extension classes
from `CategoryTheory/Preadditive/Projective/Basic.lean` and
`CategoryTheory/Preadditive/Injective/Basic.lean` at Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` (lines 48–49 and 32–33),
registered as `mathlib-projective-basic-5ed296525643` and
`mathlib-injective-basic-5ed296525643`. `Projective P` says that for
every epimorphism `e : E ⟶ X` and every `f : P ⟶ X` there exists
`f' : P ⟶ E` with `f' ≫ e = f`. `Injective P` says that for every
monomorphism `f : X ⟶ Y` and every `g : X ⟶ P` there exists
`h : Y ⟶ P` with `f ≫ h = g`. These descriptions specify the
comparisons' provenance; their equivalence to exactness remains to be
proved by the proof successor. No lifting premise is added to a theorem
in order to claim that comparison.

The aggregate is the right-associated conjunction in the same order:

```lean
def HomExactnessComparisonStatement (P : C) : Prop :=
  CovariantHomLeftExactStatement P ∧
    ContravariantHomLeftExactStatement P ∧
    HomProjectiveComparisonStatement P ∧
    HomInjectiveComparisonStatement P
```

All four clauses are conclusions. The full aggregate has only the common
category and abelian binders and the object `P`; it has no projectivity,
injectivity, exactness or aggregate hypothesis. The conjunction is
internal packaging of the two source assertions and two derived
identifications.

## Boundary

This file contains proposition definitions only. Compilation and full
declaration inspection establish that they elaborate and return `Prop`;
they do not prove any clause. A distinct exact proof successor must
prove the published aggregate and provide named proofs of its clauses.
Independent semantic review and publication are required.

Generator/cogenerator comparisons, the projective nonzero-Hom criterion,
smallness and coproduct preservation, finite-type comparisons,
presentations and module-category equivalence remain separate obligations
under the whole-book parent task. This statement unit imports neither a
pending faithfulness proof nor a finite-preservation proof.
