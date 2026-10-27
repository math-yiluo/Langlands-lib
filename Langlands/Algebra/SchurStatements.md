# Renard B.II: Schur's lemma, unital core

`Langlands/Algebra/SchurStatements.lean` states, as `Prop`-valued definitions,
the unital core of Schur's lemma in Renard's Appendix B.II. It states the two
parts of the theorem, the elementary bijectivity step, and the cyclic-map,
evaluation-map and countable-dimension auxiliaries that the proof uses. None of
these assertions is proved or assumed here. The file also proves three short
lemmas about how the maps involved behave.

## Source and errata

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The whole of Appendix B.II, printed page 272 / PDF page 278, was read as extracted
text and as a rendered image. Also read were the ring and module conventions of
Chapter I (printed pages 5–6 / PDF pages 11–12) and the definition of simple
objects in A.VI.3 (printed page 263 / PDF page 269).

The current Library has no `notes/errata` file for this source. The registered
2010-edition list *corrections et compléments*, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, was also
checked. Its entry for 2010 page 314 runs from PDF page 18 to PDF page 19. It says
that `M` must also be assumed to be a complex vector space, because `A` has no
unit. It also says the proof may reduce to unital `A` and a unital `M` by passing
to `Ã = A ⊕ ℂ1_A` as in I.2.1. The 2026 text already contains both corrections.
That list belongs to a different edition, so the 2026 text governs here.

## The source passage

> **B.II Lemme de Schur**
>
> Soit *A* une ℂ-algèbre (que l'on ne suppose pas forcément unitaire). Nous allons
> utiliser le résultat de la section précédente pour montrer le
>
> **Théorème.** *Soit M un A-module simple et un ℂ-espace vectoriel. On a alors*
> *a) End_A(M) est une algèbre à division.*
> *b) Si la dimension de M sur ℂ est au plus dénombrable, on a End_A(M) ≃ ℂ.*
> *Il suffit pour cela que la dimension de A soit au plus dénombrable.*
>
> *Démonstration.* Remarquons tout d'abord que quitte à remplacer *A* par
> *Ã = A ⊕ ℂ1_A* où comme dans la section I.2.1 on ajoute une unité à *A*, on peut
> supposer que *A* est une algèbre unitaire et *M* un *A*-module unitaire.
>
> Soit 0 ≠ *f* ∈ End_A(M). Comme ker *f* et Im *f* sont des sous-modules de *M*, et
> que *M* est simple, on a ker *f* = 0 et Im *f* = *M*. Ceci montre que *f* est
> inversible.
>
> Montrons maintenant que si la dimension de *A* est au plus dénombrable, il en est
> de même de celle de *M*. Considérons *m* ∈ *M* tel que *A·m ≠ 0* et
> *A → M, a ↦ a·m*. Comme *M* est simple, *A·m = M* et donc *M* est de dimension au
> plus dénombrable sur ℂ.
>
> De même, démontrons b) : considérons *End_A(M) → M, f ↦ f(m)*. Comme
> *f(a·m) = a·f(m)* et que *A·m = M*, on voit que *f* est déterminé par *f(m)*, et
> donc que le morphisme ci-dessus est injectif. On en déduit que la dimension de
> End_A(M) est au plus dénombrable. Le théorème d'Amitsur, montre alors que
> End_A(M) ≃ ℂ. □

## Scope: only the unital core

Renard's algebra `A` need not be unital. Its action on `M` is not assumed unital
either, and may even be zero. The proof starts by replacing `A` with its
unitization `Ã = A ⊕ ℂ1_A` (I.2.1), on which `M` becomes a unital module. This file
states **only the resulting unital core**: `A` is a unital ring and `M` is an
ordinary unital `A`-module (Lean's `Module A M`). These targets alone do **not**
cover Renard's original nonunital statement. The parent program keeps the
following work: the compatible complex-linear ambient nonunital action, the actual
unitized action of `Ã`, the comparison of stable complex subspaces, of simplicity
and of endomorphisms between `A` and `Ã`, and the passage from countable dimension
of `A` to countable dimension of `Ã`. The published additive interface in
`Langlands/Algebra/NonUnitalModule.lean` is not used or changed here.

## Conventions

* `A : Type u` and `M : Type v` live in independent universes; `ℂ` stays in
  `Type`. All binders are explicit header binders of each definition, never
  section variables.
* **Simple module.** In A.VI.3 Renard defines a simple object as a nonzero object
  whose only subobjects are `0` and itself. For a unital module this is Mathlib's
  `IsSimpleModule A M`: the submodule lattice is a simple order, so `M ≠ 0` and
  every submodule is `⊥` or `⊤`. Every target carries `IsSimpleModule A M` as a
  premise **inside its proposition**. It is never an unused section instance,
  which Lean would silently drop.
* **Complex structure.** In the complex targets, `[Algebra ℂ A]` makes `A` a
  unital complex algebra, not necessarily commutative. `[Module ℂ M]` is the
  complex vector-space structure of `M`, and `IsScalarTower ℂ A M` says the two
  are compatible: `(z • a) • m = z • (a • m)`. Through Mathlib's `SMulCommClass`
  instance, this compatibility gives the actual complex structure on
  `Module.End A M`, the canonical algebra `Module.End.instAlgebra`. It is also
  what makes the restricted cyclic map and the evaluation map complex-linear.
* **Dimension at most countable** is the cardinal-valued rank bounded by
  `Cardinal.aleph0` in the carrier's own universe:
  `Module.rank ℂ A ≤ Cardinal.aleph0` in `Cardinal.{u}`, and
  `Module.rank ℂ M ≤ Cardinal.aleph0` and
  `Module.rank ℂ (Module.End A M) ≤ Cardinal.aleph0` in `Cardinal.{v}`
  (`Module.End A M : Type v`). No `finrank` is used, countability of the
  underlying set is not required, and no ranks in different universes are
  compared.
* **`End_A(M) ≃ ℂ`.** As in B.I ("On identifie la sous-algèbre ℂ1_A de A avec
  ℂ"), the identification is the canonical one. It is stated as bijectivity of
  the actual map `algebraMap ℂ (Module.End A M)`, which sends `z` to the
  endomorphism `m ↦ z • m`. The proved lemma `bijective_algebraMap_end_iff`
  shows that this bijectivity means exactly that every `A`-linear endomorphism
  is scalar multiplication by a unique complex number. An arbitrary equivalence
  `Module.End A M ≃ ℂ` would not express the source's claim.
* **Division algebra.** "End_A(M) est une algèbre à division" is stated as
  `Nontrivial (Module.End A M)` together with "every nonzero endomorphism is a
  unit" (`IsUnit`) in the monoid `Module.End A M`. These are the defining
  properties of a division ring.

## Declarations

All are in namespace `Langlands.Renard`. The eight targets, in the order of the
task, are:

1. `SchurEndDivisionStatement A M` for `(A : Type u) [Ring A] (M : Type v)
   [AddCommGroup M] [Module A M]`: `IsSimpleModule A M → Nontrivial (Module.End A M) ∧
   ∀ f : Module.End A M, f ≠ 0 → IsUnit f`. This is **Théorème a)**.
2. `SchurEndBijectiveStatement A M`, with the same binders:
   `IsSimpleModule A M → ∀ f : Module.End A M, f ≠ 0 → Function.Bijective f`.
   This is the first step of the proof (`ker f = 0`, `Im f = M`).

   The remaining targets take `(A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
   [AddCommGroup M] [Module A M] [Module ℂ M]`. All except 5 also take the
   typeclass binder `[IsScalarTower ℂ A M]`, which they need to form their maps
   and the complex algebra `Module.End A M`.

3. `SchurCyclicMapSurjectiveStatement A M`: `IsSimpleModule A M → ∀ m : M, m ≠ 0 →
   Function.Surjective ((LinearMap.toSpanSingleton A M m).restrictScalars ℂ)`.
   This is the complex-linear action map `A → M, a ↦ a • m`
   (`schur_cyclicMap_apply`), with "*A·m = M*". For a unital module, the
   source's choice "*A·m ≠ 0*" is equivalent to `m ≠ 0`, because `1 • m = m`.
4. `SchurEvaluationInjectiveStatement A M`: `IsSimpleModule A M → ∀ m : M, m ≠ 0 →
   Function.Injective (LinearMap.applyₗ' ℂ m : Module.End A M →ₗ[ℂ] M)`. This is
   the complex-linear evaluation map `f ↦ f m` (`schur_evaluation_apply`) of the
   proof of b).
5. `SchurModuleRankCountableStatement A M`: `IsScalarTower ℂ A M →
   IsSimpleModule A M → Module.rank ℂ A ≤ Cardinal.aleph0 →
   Module.rank ℂ M ≤ Cardinal.aleph0`. This is the transfer of countable dimension
   from `A` to `M`. Its conclusion mentions only ranks, so a typeclass binder for
   the compatibility would be unused and dropped by Lean. The compatibility is
   therefore an explicit premise of the proposition. Without it, the complex
   structure of `M` would bear no relation to that of `A`, and the source's
   argument would not apply.
6. `SchurEndRankCountableStatement A M`: `IsSimpleModule A M →
   Module.rank ℂ M ≤ Cardinal.aleph0 →
   Module.rank ℂ (Module.End A M) ≤ Cardinal.aleph0`. This is the transfer of
   countable dimension from `M` to `End_A(M)`, deduced in the source from 4.
7. `SchurScalarOfModuleRankCountableStatement A M`: `IsSimpleModule A M →
   Module.rank ℂ M ≤ Cardinal.aleph0 →
   Function.Bijective (algebraMap ℂ (Module.End A M))`. This is **Théorème b)**.
8. `SchurScalarOfAlgebraRankCountableStatement A M`: `IsSimpleModule A M →
   Module.rank ℂ A ≤ Cardinal.aleph0 →
   Function.Bijective (algebraMap ℂ (Module.End A M))`. This is the last sentence
   of the theorem, "Il suffit pour cela que la dimension de A soit au plus
   dénombrable".

The entry declaration, with the same binders as 3–8, is

* `SchurTheoremStatement A M := SchurEndDivisionStatement A M ∧
  SchurScalarOfModuleRankCountableStatement A M ∧
  SchurScalarOfAlgebraRankCountableStatement A M`. This is the whole Théorème
  (a and both alternatives of b) for the unital core.

### Proved lemmas

These lemmas concern the maps only; they prove none of the assertions above.

* `schur_cyclicMap_apply`:
  `((LinearMap.toSpanSingleton A M m).restrictScalars ℂ) a = a • m` (`rfl`).
* `schur_evaluation_apply`:
  `(LinearMap.applyₗ' ℂ m : Module.End A M →ₗ[ℂ] M) f = f m` (`rfl`).
* `bijective_algebraMap_end_iff`:
  `Function.Bijective (algebraMap ℂ (Module.End A M)) ↔
  ∀ f : Module.End A M, ∃! z : ℂ, ∀ m : M, f m = z • m`. The proof rewrites
  bijectivity as unique existence of preimages
  (`Function.bijective_iff_existsUnique`). It then compares
  `algebraMap ℂ _ z = f` pointwise (`LinearMap.ext_iff`), where
  `algebraMap ℂ _ z m` is definitionally `z • m`.

## Provenance of the ring-only forms

Targets 1 and 2 use only `[Ring A]` and `[Module A M]`. The source's argument for
a), via kernel, image and simplicity, uses no complex structure, so these forms
generalize the source's first argument to arbitrary unital rings. Every unital
complex algebra is in particular a ring, so they specialize to the source's
setting. The source's complex vector-space hypothesis on `M` serves only the
unitization and part b). Targets 2–6 are not separately numbered claims of the
source; they are the intermediate assertions its proof explicitly makes, stated
here so that later proofs can be split along the source's argument.

## Verification

Every target was compiled in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
and inspected with `statement_returns_prop: true` and only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). A private diagnostic printed the
complete `@`-types and expanded bodies of all nine definitions. It confirmed the
following points:

* `IsSimpleModule A M` occurs in every body;
* `IsScalarTower ℂ A M` is a binder of targets 3, 4, 6, 7, 8 and of the entry,
  and a premise in the body of target 5;
* the maps are the actual `LinearMap.toSpanSingleton` restricted to `ℂ`,
  `LinearMap.applyₗ'` and `algebraMap`;
* the universe parameters `u` and `v` are independent, which was checked by
  instantiating them with different universes.

Private sanity checks, not part of this file, also proved targets 1–3 directly
from Mathlib. They confirm that these propositions are neither vacuous nor
misstated.

## Not claimed; future proof routes

Nothing here proves Schur's lemma or a dimension transfer. A later proof may use
Mathlib's simple-module results, such as `LinearMap.bijective_of_ne_zero`,
`Module.End.instDivisionRing` and `IsSimpleModule.toSpanSingleton_surjective`.
For scalarity it may also use the separate Amitsur division-algebra target
`Langlands.Renard.AmitsurDivisionAlgebraStatement` (module
`Langlands.Algebra.AmitsurStatements`), once that target is proved. These are
proof obligations, not hypotheses of the present targets. No topology, finite
dimension, commutativity of `A` or group origin is assumed. The Library's
`Langlands.countableDimensionalSchur` concerns irreducible group representations
specifically and is not used.

## Attribution

The candidate types follow a private type probe by Worker 6
(`schur-feasibility/SchurProbe.lean`, diagnostic
`7978c47a-1e7b-4607-94d3-294f6395307c`). Worker 713 reread the source, wrote this
file, added the entry conjunction and the proved map lemmas, and repeated the
complete type inspection.
