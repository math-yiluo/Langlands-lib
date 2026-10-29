# B-linear universal property of the localized algebra action

Authors: Worker 926 and Worker 709, for task
`43950ba3-b202-4a68-94f2-885fbcd81582`, revision 2. Worker 709 wrote an
earlier private statement design. This unit reuses its module name,
declaration names, explicit binder layout, field interface and aggregate
conjunction. Worker 926 reread the source passages and changed the operator
condition to the pointwise form the task requires. Worker 926 also made the
field statement use the published field constructor, ran the checks and wrote
this Markdown.

The module `Langlands/Algebra/RenardAlgebraLocalizationUniversalStatements.lean`
contains three Prop-valued definitions in namespace
`Langlands.Renard.AlgebraActionLocalization`. They state the B-linear
universal property of the published compatible action on the localization of
an endomorphism. The module contains no proof and no new construction.

## Original source

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated **9 July 2026**. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`; file:
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`;
SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Printed body page = PDF page minus 6.

Worker 926 reread these passages for this unit:

- A.III.1, printed p. 251 / PDF p. 257: the definition of a solution `(X, i)`
  of the right universal problem posed by a functor F and an object Y. For
  every object Z and morphism `f : Y → F(Z)` there is a unique morphism
  `g : X → Z` with `F(g) ∘ i = f`.
- A.III.1, example 5, printed p. 252 / PDF p. 258. Objects are pairs
  `(L, a)` with `a ∈ End_k(L)`. Morphisms `(L, a) → (L', a')` are linear maps
  intertwining a and a'. The example gives a pair `(L_a, ã)` with ã invertible
  and a morphism `ι : (L, a) → (L_a, ã)`. For every morphism
  `f : (L, a) → (M, b)` with `b ∈ End_k(M)` invertible, there is a unique
  morphism `f̃ : (L_a, ã) → (M, b)` with `f = f̃ ∘ ι`.
- The final sentence of example 5: « Si B est une k-algèbre, on peut faire la
  même construction en remplaçant les k-espaces vectoriels par des B-modules,
  et les endomorphismes d'espaces vectoriels par des endomorphismes de
  B-modules. »
- The global conventions on printed pp. 5–6 / PDF pp. 11–12. Rings are not
  assumed unital unless stated. Modules over a unital ring are not assumed
  unital.

This unit states the universal-property part of that final sentence. The
same B-module version is formed from B-modules, B-module endomorphisms and
B-module maps intertwining the endomorphisms. The final sentence adds no unit,
commutativity or nondegeneracy hypothesis on B or on its modules.

The registered supplementary source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked by Worker 926 on PDF pp. 15 and 17–19 for the published
construction. No correction to A.III.1 example 5 was found. This is a limited
reading of the errata of an older edition; the 2026 original governs.

## Formal encoding and derived content

The following choices are **derived formalization content**, not formulas
quoted from the book.

- **B-modules.** As in the published construction
  `Langlands.Algebra.RenardAlgebraActionLocalization`, a B-module is a
  k-module V with an actual nonunital k-algebra homomorphism
  `ρ : B →ₙₐ[k] Module.End k V`. B-module maps are actual
  `Langlands.Algebra.LinearIntertwiner` objects: k-linear maps commuting with
  every action map. A B-module endomorphism of the source is a k-linear
  `a : Module.End k V` with `ha : ∀ b z, a (ρ b z) = ρ b (a z)`.
- **Invertible target endomorphism.** The source's invertible
  `b ∈ End_B(M)` is the Lean variable c, renamed to avoid a clash with
  algebra elements. It is an actual `c : LinearIntertwiner σ σ` with
  `IsUnit c.toLinearMap` in the ring `Module.End k W`. This is equivalent to
  invertibility among B-module endomorphisms. If d is a k-linear inverse of c,
  then `d (σ b w) = d (σ b (c (d w))) = d (c (σ b (d w))) = σ b (d w)`. So d is
  automatically B-linear. The statement does not assume this B-linearity; a
  proof must derive whatever it needs.
- **The localized pair and ι.** The pair `(L_a, ã)` is the published carrier
  `Langlands.Renard.EndomorphismLocalization.Localized a` with the published
  action `localizedAction a ρ ha` and operator `localizedEnd a`. The morphism ι
  is the published `iotaIntertwiner a ρ ha`, whose underlying linear map is
  `iota a`. The statements reuse these objects; they do not replace them. The
  published `isUnit_localizedEnd a` and `localizedEndIntertwiner a ρ ha` already
  show that ã is invertible and B-linear. So `(L_a, ã)` lies in the target class.
  The statements here assert only the universal factorization.
- **Morphisms of pairs.** A morphism `(L_a, ã) → (W, c)` is encoded as
  `g : LinearIntertwiner (localizedAction a ρ ha) σ` together with the
  pointwise equation `∀ z, g (localizedEnd a z) = c (g z)`. The equation
  `f = f̃ ∘ ι` is `g.comp (iotaIntertwiner a ρ ha) = f`. By intertwiner
  extensionality, the pointwise equation is equivalent to Worker 709's bundled
  form `g.comp (localizedEndIntertwiner a ρ ha) = c.comp g`. The evaluated form
  of the second equation is `∀ v, g (iota a v) = f v`. Worker 926 checked
  both equivalences in a private development file; they are not declarations
  of this unit.
- **Coefficients and universes.** The general statement allows a commutative
  ring k. The field statement is the source-facing case. Universes are
  independent: `k : Type u`, `B : Type v`, `V : Type w`, `W : Type x`. The
  published carrier `Localized a` lies in `Type (max u w)`. The target W need
  not share its universe or be related to V.

## Hypotheses retained and not assumed

The general statement uses exactly

```text
k : Type u, B : Type v, V : Type w, W : Type x
[CommRing k] [NonUnitalRing B] [Module k B]
[AddCommGroup V] [Module k V]
[AddCommGroup W] [Module k W]
a : Module.End k V
ρ : B →ₙₐ[k] Module.End k V
ha : ∀ b z, a (ρ b z) = ρ b (a z)
σ : B →ₙₐ[k] Module.End k W
c : LinearIntertwiner σ σ
IsUnit c.toLinearMap
f : LinearIntertwiner ρ σ
∀ z, f (a z) = c (f z)
```

These are the general hypotheses of the published `localizedAction`. Only
`[Module k B]` is required on B besides `[NonUnitalRing B]`; the general helpers
do not use k-bilinearity of B's multiplication. The field statement keeps
the complete source interface

```text
[Field k] [NonUnitalRing B] [Module k B]
[IsScalarTower k B B] [SMulCommClass k B B]
```

and the same remaining data.

No statement assumes that B is unital or commutative. None assumes that ρ or
σ is nondegenerate or unital. None assumes finite dimension, finite generation
or noetherianity. Zero actions, zero spaces and an arbitrary source operator
a, for example zero, nilpotent or noninjective, are allowed. Only the target
operator c is assumed invertible.

No hypothesis says that the published scalar-linear factor
`Langlands.Renard.EndomorphismLocalization.factor` is B-linear. No hypothesis
supplies a factorization or the B-linearity of the inverse of c. These belong
to the later proof.

## Statement declarations

`UniversalPropertyStatement` quantifies over all the general data and
hypotheses above. It concludes

```text
∃! g : LinearIntertwiner (localizedAction a ρ ha) σ,
  (∀ z, g (localizedEnd a z) = c (g z)) ∧
    g.comp (iotaIntertwiner a ρ ha) = f
```

Both equations are inside the unique-existence predicate. So uniqueness is
taken among actual linear intertwiners of the localized action that
intertwine `localizedEnd a` with c and factor f through the canonical map.
This matches the morphisms of pairs in the source universal problem.

`FieldUniversalPropertyStatement` is the same closed assertion over an
arbitrary field k with the complete bilinear algebra interface. Its factor has
type `LinearIntertwiner (fieldLocalizedAction a ρ ha) σ`, using the published
source-facing constructor. The composite with `iotaIntertwiner a ρ ha`
type-checks because `fieldLocalizedAction a ρ ha` is by definition
`localizedAction a ρ ha`; the published `fieldLocalizedAction_eq` proves this
by `rfl`. The field statement follows from the general one by instantiation;
a private development check confirmed this. It is a source-facing
specialization, not an additional source result.

`UniversalPropertyStatements` is the conjunction
`UniversalPropertyStatement.{u, v, w, x} ∧ FieldUniversalPropertyStatement.{u, v, w, x}`
with all four universe parameters. The later exact-target proof task should
prove this aggregate.

## Reuse, checks and remaining obligations

The module imports the published
`Langlands.Algebra.RenardAlgebraActionLocalization` by Lean name. That module
was implemented by Workers 709 and 926 and imports the scalar-linear
localization `Langlands.Algebra.RenardEndomorphismLocalization` and the
compatible-action API `Langlands.Algebra.CompatibleNonUnitalAction`, both
implemented by Worker 751. Their full attribution, including Worker 709's
contributions, is recorded in their paired Markdown. This module
copies no implementation bodies and introduces no axioms.

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` the module compiled with
no errors or warnings. Inspection of `UniversalPropertyStatements` reported
`statement_returns_prop: true`, independent universe parameters u, v, w and x,
and only the axioms `propext`, `Classical.choice` and `Quot.sound`. These
checks are development evidence, not semantic acceptance.

A private draft proof by Worker 926 also compiled in that environment, using
only those three axioms; it was not submitted. Its route takes the published
scalar factor of f through the invertible c. It then applies `factor_unique`
to both `g₀ ∘ localizedAction a ρ ha b` and `σ b ∘ g₀` to get B-linearity, and
uses `factor_unique` again for uniqueness. This module neither contains nor
depends on that proof; the proof is the obligation of a separate task.

Kernel and quotient descriptions, the converse characterization, the
surjective-canonical-map corollary, categorical packaging, localization
exactness and the finite-localization proposition of C.II remain separate
obligations. This unit makes no whole-book coverage claim.
