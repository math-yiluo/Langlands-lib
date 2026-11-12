# Renard I.2.2: exactness of the tensor and Hom functors on nondegenerate modules

Module `Langlands.Algebra.NondegenerateTensorHomExactnessStatements`.
Namespace `Langlands.Algebra.NondegenerateTensorHomExactness`.
Entry proposition `Statements`.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read I.2.2 on printed pp.15–16 / PDF pp.21–22 for this unit. The
assertion is the unnumbered Proposition of I.2.2, printed p.15 / PDF p.21:

> **Proposition.** Soit `A` une ℂ-algèbre à idempotents, et `X` un `A`-module
> non dégénéré.
> Le foncteur `• ⊗_A X` est covariant et exact à droite,
> le foncteur `Hom_A(•, X)` est contravariant et exact à gauche,
> le foncteur `Hom_A(X, •)` est covariant et exact à gauche.

Just before it, the source introduces these functors for a unital algebra:
`• ⊗_A X : M(A)_d → ℂ-Ev`, `Y ↦ Y ⊗_A X`, and `Hom_A(•, X)`,
`Hom_A(X, •) : M(A) → ℂ-Ev`. Here `M(A)` (resp. `M(A)_d`) is the category of
nondegenerate left (resp. right) `A`-modules. The source refers to [34],
pp.218–219, for the proof. Exactness of a functor is defined in A.VIII.1,
printed p.266 / PDF p.272, by preservation of one-sided exact sequences.

The source works over complex algebras and lands in complex vector spaces.
This unit works over an arbitrary associative `NonUnitalRing A` and lands in
integer modules, as the published Hom functors of A.VIII.2 do. A sequence of
complex vector spaces is exact if and only if its underlying sequence of
abelian groups is exact, so nothing is lost. The idempotented hypothesis and
nondegeneracy of `X` are kept, as in the source.

## Helper construction: `tensorFunctor A X`

For a left module `X` (`[NonUnitalModule A X]`), `tensorFunctor A X` is the
functor `NondegenerateModuleCat Aᵐᵒᵖ ⥤ ModuleCat ℤ` that sends a nondegenerate
right module `Y` to `ModuleCat.of ℤ (NonUnitalModuleTensor.Tensor A Y.obj X)`,
the published balanced tensor `Y ⊗_A X` with its integer-module structure.
A morphism `f : Y ⟶ Y'` goes to `NonUnitalModuleTensor.map A f.hom id_X`, the
published map `f ⊗ id_X` (as an integer-linear map). The functor laws are the
published `NonUnitalModuleTensor.map_id` and `map_comp`.
`tensorFunctor_obj` and `tensorFunctor_map_hom` record the definitions.
`map_add_id` proves that `f ↦ f ⊗ id_X` is additive, from
`NonUnitalModuleTensor.hom_ext` and `add_tmul`. The instance
`tensorFunctor_additive` makes the functor additive, which the exactness
predicate requires. The carrier universe is `max uY uX`.

A right module is a `NonUnitalModule Aᵐᵒᵖ`, as in the published modules.

## Proposition definitions

Each predicate is the published `Langlands.Renard.SequenceRightExact`,
`SequenceLeftExact` or `ContravariantSequenceLeftExact` of A.VIII.1. The
abelian structure on `M(A)` is the published
`NondegenerateModuleCat.abelian A hA`, and on `M(A)_d` it is
`NondegenerateModuleCat.abelian Aᵐᵒᵖ hA.op`. Integer modules carry Mathlib's
abelian structure.

### `TensorRightExactStatement`

For an idempotented ring `A` (`hA : IsIdempotented A`) and a nondegenerate
left module `X` (`IsNondegenerate A X`), `SequenceRightExact (tensorFunctor A X)`:
every exact sequence `Y₁ → Y₂ → Y₃ → 0` of nondegenerate right modules goes to
an exact sequence `Y₁ ⊗_A X → Y₂ ⊗_A X → Y₃ ⊗_A X → 0`.

### `ContravariantHomLeftExactStatement`

For idempotented `A` and an object `X` of `M(A)`,
`ContravariantSequenceLeftExact (preadditiveYonedaInt X)`, where
`preadditiveYonedaInt X : M(A)ᵒᵖ ⥤ ModuleCat ℤ` is the published Hom functor
`Hom_A(•, X)` of A.VIII.2.

### `CovariantHomLeftExactStatement`

For idempotented `A` and an object `X` of `M(A)`,
`SequenceLeftExact (preadditiveCoyonedaInt X)`, for the published Hom functor
`Hom_A(X, •) : M(A) ⥤ ModuleCat ℤ` of A.VIII.2.

The two Hom clauses are the specializations to `M(A)` of the published
general A.VIII.2 statements `Langlands.Renard.ContravariantHomLeftExactStatement`
and `Langlands.Renard.CovariantHomLeftExactStatement`, which hold in every
abelian category. They are restated here so that the whole I.2.2 Proposition
has one entry statement.

### `Statements`

`Statements.{uA, uX, uY, uM}` is the conjunction of the three clauses, in the
source's order. The ring universe `uA`, the fixed-module universe `uX`, the
right-module universe `uY` and the Hom-clause carrier universe `uM` are
independent.

## Scope and dependencies

This file states the Proposition and proves none of it. Proofs belong to a
separate `lean.proof@1` task targeting `Statements`. The other I.2.2
assertions, the Theorem (I.2.2.1)–(I.2.2.4) and the Corollary
(I.2.2.5)–(I.2.2.7), have published additive statements in
`NonUnitalTensorHomAdjunctionStatements` and
`NonUnitalTensorAssociativityStatements`; their coefficient and unitization
comparisons remain open, as recorded there.

The file imports `Langlands.Algebra.NonUnitalModuleTensor`,
`Langlands.Algebra.NondegenerateModuleAbelianProof`,
`Langlands.CategoryTheory.Renard.HomExactnessComparisonStatements` and pinned
Mathlib `Mathlib.Algebra.Category.ModuleCat.Abelian` (environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
