# Renard I.3.2: simple modules and the equivalence criterion for `j_e`

Module `Langlands.Algebra.NonUnitalModuleCornerSimpleStatements`.
Namespace `Langlands.Algebra.NonUnitalModuleCornerSimpleStatements`.
Entry proposition `Statements`.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read I.3.1–I.3.2 on printed pp.19–22 / PDF pp.25–28 for this unit.
The two assertions stated here are on printed pp.21–22 / PDF pp.27–28:

> **Proposition.** L'application `M ↦ e·M` réalise une bijection entre
> `Irr(A, e)` et `Irr(eAe)`, dont l'inverse est donnée par
> `W ↦ (A ⊗_{eAe} W)_e`.

> **Théorème.** Le foncteur `j_e` est une équivalence de catégories entre
> `M(A, e)` et `M(eAe)` si et seulement si la sous-catégorie `M(A, e)` de
> `M(A)` est stable par passage aux sous-quotients (en particulier, c'est alors
> une catégorie abélienne). Le foncteur inverse est donné par le foncteur
> `i = P^A_{eAe}`.

Printed p.19 / PDF p.25 sets the notation: `A` is a complex algebra with
idempotents and `e ∈ Idem(A)`; `M(A, e)` is the full subcategory of `M(A)` of
modules with `M = Ae·M`; `Irr(A)` is the set of isomorphism classes of
nondegenerate simple `A`-modules; `Irr(eAe)` is the set of isomorphism classes
of simple unital `eAe`-modules; `Irr(A, e)` is the subset of `Irr(A)` of the
classes with `e·M ≠ 0`. Printed p.20 / PDF p.26 defines
`M_e = M / F(eA, M)` with `F(eA, M) = {m ∈ M | eA·m = 0}`.

The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF
pp.1–2, corrects the 2010 proofs of (I.3.2.1) and of this Proposition
(`F(eA, A ⊗_{eAe} e·M)` in place of `F(eA, M)`, and the missing surjectivity
and maximality arguments). The 2026 text already contains these corrections.
They concern proofs, not the statements here.

The source works over complex algebras. All objects below are the published
constructions over an arbitrary associative `NonUnitalRing A`; `ℂ` plays no
role in either assertion. The internal formal choices are explained below:
the clause decomposition of the Proposition, the omission of the
idempotented hypothesis in one clause, the categorical form of "stable par
passage aux sous-quotients", the form of the inverse-functor and abelian
clauses, and the carrier universe of the Theorem.

## The objects

All declarations come from the Library; this file constructs nothing.

- `M(A)` is `NondegenerateModuleCat A`: modules with every vector fixed by an
  idempotent (`IsNondegenerate`). A simple object of `M(A)` is a
  `CategoryTheory.Simple` object of this category, as in the published
  `NonUnitalModuleAdmissibilityStatements`.
- `e·M` is `NonUnitalModuleCorner.FixedPart e M` with its published unital
  `Idempotent.Corner e`-module structure `fixedPartModule`. `eAe` is
  `Idempotent.Corner e`, and `M(eAe)` is `ModuleCat (Idempotent.Corner e)`.
  `Nontrivial (FixedPart e M)` says `e·M ≠ 0`.
- `A ⊗_{eAe} W` is `NonUnitalModuleCornerInduction.Tensor e W` with
  `tensorAddCommGroup` and `tensorModule`; `tmul e a w` is `a ⊗ w`.
  `nondegenerateObject hA e W` is the same object in `M(A)`.
- `M_e` is `annihilatorQuotientCarrier e M`, with projection
  `annihilatorQuotientProjection e M`; in `M(A)` it is the published functor
  `NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor e`.
- `φ` (and `ψ_V`) is `NonUnitalModuleCornerEvaluation.evaluation e M`, the
  intertwiner `A ⊗_{eAe} e·M → M`, `a ⊗ e·m ↦ a·e·m`.
- `M(A, e)` is `NonUnitalModuleIdempotentGenerated.GeneratedModuleCat e`, the
  full subcategory of `M(A)` given by the object property
  `generatedProperty e` (`IsGeneratedByIdempotent`: every vector lies in the
  published additive submodule `AeM`). `j_e` on it is `cornerFunctor e`.

## The Proposition

The Proposition is stated as four closed propositions. Together with the
functoriality of `M ↦ e·M` and `W ↦ (A ⊗_{eAe} W)_e` (published functors),
they say exactly that `M ↦ e·M` is a well-defined bijection
`Irr(A, e) → Irr(eAe)` with inverse `W ↦ (A ⊗_{eAe} W)_e`:
the two maps land in the right sets, and both composites return an
isomorphic module. Each isomorphism is given by the source's explicit map.

### `SimpleFixedPartStatement`

For an idempotented ring `A` (`IsIdempotented A`), an idempotent `e`, and a
nondegenerate module `M` that is a simple object of `M(A)` with
`Nontrivial (FixedPart e M)`, the corner module `FixedPart e M` is simple
(`IsSimpleModule (Idempotent.Corner e)`). This is the first paragraph of the
proof: `M ↦ e·M` maps `Irr(A, e)` into `Irr(eAe)`.

### `SimpleInducedQuotientStatement`

For idempotented `A`, an idempotent `e` and a simple unital
`Idempotent.Corner e`-module `W`, the object `(A ⊗_{eAe} W)_e` of `M(A)`
(the published quotient functor applied to `nondegenerateObject hA e W`) is
simple, and its fixed part is nontrivial. This is the second part of the
proof: `W ↦ (A ⊗_{eAe} W)_e` maps `Irr(eAe)` into `Irr(A, e)`.

### `FixedPartInducedQuotientStatement`

For every ring `A`, idempotent `e` and unital `Idempotent.Corner e`-module
`W`, there is an `Idempotent.Corner e`-linear equivalence
`E : W ≃ₗ FixedPart e ((A ⊗_{eAe} W)_e)` with
`(E w).val = [e ⊗ w]` (the projection of `tmul e e w`). This is the source's
`W ≃ e·(A ⊗_{eAe} W)_e`, obtained by composing (I.3.2.1) with the
isomorphism (I.3.2.2). The source states it inside the proof for simple `W`;
its argument uses neither simplicity nor local units, so the clause assumes
neither. The two published inputs are
`NonUnitalModuleCornerInduction.CornerInductionFixedPartEquivalenceTheorem`
and `IdempotentAnnihilatorFixedPartComparisonTheorem`.

### `InducedQuotientFixedPartStatement`

For idempotented `A`, an idempotent `e` and a simple object `M` of `M(A)` with
`Nontrivial (FixedPart e M)`, there is an intertwiner
`φbar : (A ⊗_{eAe} e·M)_e → M` with `φbar ∘ π = evaluation e M` (where `π` is
the quotient projection) that is bijective. This is the source's
`φ̄ : (A ⊗_{eAe} e·M)_e → M`, `a ⊗ e·m ↦ a·e·m`, "injectif et reste surjectif,
c'est donc un isomorphisme".

### `SimpleCorrespondenceStatement`

The conjunction of the four clauses above.

## The Theorem

### `CornerEquivalenceCriterionStatement`

For idempotented `A` and an idempotent `e`:
`(cornerFunctor e).IsEquivalence` holds if and only if
`(generatedProperty e).IsClosedUnderSubobjects` and
`(generatedProperty e).IsClosedUnderQuotients` hold, both in `M(A)`.

These are Mathlib's classes: for every monomorphism `X ⟶ Y` of `M(A)` with
`Y` in `M(A, e)`, also `X` is; for every epimorphism `X ⟶ Y` of `M(A)` with
`X` in `M(A, e)`, also `Y` is. A subquotient is a quotient of a subobject, so
closure under both is closure under subquotients.

Carriers live in the universe `max uA uM`, which contains the universe of
`A`. This is a formal choice. The source's sufficiency proof uses
`i(Z) = A ⊗_{eAe} Z`, whose carrier lies in `max uA uZ`. Below the universe
of `A` the criterion can fail for size reasons: for the algebra of
finite-rank operators on a vector space too large for the carrier universe, the
only nondegenerate modules of that universe are zero, while unital
`eAe`-modules for a rank-one `e` are all vector spaces of that universe.

### `GeneratedCategoryAbelianStatement`

For idempotented `A` and `e`, if `generatedProperty e` is closed under
subobjects and quotients, then there is an `Abelian` structure on
`GeneratedModuleCat e` whose underlying preadditive structure is the
inherited one. This is "en particulier, c'est alors une catégorie abélienne".

### `CornerInductionInverseStatement`

For idempotented `A` and `e`, if `generatedProperty e` is closed under
subobjects and quotients, then for every object `V` of `M(A, e)` the
evaluation `ψ_V = evaluation e V : A ⊗_{eAe} e·V → V` is bijective. This is
the source's final step: "les `ψ_V` donnent un isomorphisme naturel entre
`i ∘ j_e` et l'identité de `M(A, e)`". The naturality of `ψ` is the published
`NonUnitalModuleCornerEvaluation.evaluation_naturality`, and the other natural
isomorphism `Z ≃ j_e ∘ i(Z)` is the published (I.3.2.1). So this clause makes
"le foncteur inverse est donné par le foncteur `i`" explicit.

### `CornerEquivalenceStatement`

The conjunction of the three Theorem clauses.

## `Statements`

`Statements.{uA, uM, uW}` is
`SimpleCorrespondenceStatement.{uA, uM, uW} ∧ CornerEquivalenceStatement.{uA, uM}`.
The universes `uA` (ring), `uM` (ambient module carriers) and `uW` (corner
module carriers) are independent; the Theorem uses carriers in `max uA uM`.

## Scope and dependencies

This file states the two assertions and proves neither. Proofs belong to a
separate `lean.proof@1` task targeting `Statements`.

The other assertions of I.3 are already published: the construction of `j_e`
and (I.3.1.1) in `NonUnitalModuleCorner`, the exactness Proposition of I.3.1
in `NonUnitalModuleCornerExactnessStatements` and its proof, the category
`M(A, e)` in `NonUnitalModuleIdempotentGenerated`, the Lemma (I.3.2.1) in
`NonUnitalModuleCornerInductionStatements` and its proof, the generatedness of
`i(Z)` in `NonUnitalModuleCornerInductionGeneratedStatements`, the definition
of `M_e` in `IdempotentAnnihilatorQuotient`, the Lemma `(M_e)_e = M_e` and
(I.3.2.2) in `IdempotentAnnihilatorComparisonStatements`, and the image,
surjectivity and kernel facts about `φ` in
`NonUnitalModuleCornerEvaluationStatement`.

The file imports `Langlands.Algebra.NonUnitalModuleCornerEvaluation`,
`Langlands.Algebra.NonUnitalModuleIdempotentGenerated`,
`Langlands.Algebra.IdempotentAnnihilatorQuotient.NamedCarrier`, and pinned
Mathlib `Mathlib.CategoryTheory.Simple`,
`Mathlib.CategoryTheory.ObjectProperty.EpiMono`,
`Mathlib.CategoryTheory.Abelian.Basic` and `Mathlib.RingTheory.SimpleModule.Basic`
(environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`). Like
`NonUnitalModuleCornerEvaluationStatement`, it makes the published
`rightCornerModule`, `cornerModule` and `tensorModule` local instances.
