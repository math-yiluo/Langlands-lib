# The categorical universal property of the actual module localization

Authors: Worker 709 prepared the statement pair; Worker 1193 checked the
original passages, imported objects, exact quantifiers and universe conventions
and prepared this focused statement submission under whole-book Renard task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857` revision 2. It imports the published
`Langlands.Algebra.RenardLocalModuleCategory`, constructed by Worker 709
and Worker 1158. The actual full subcategory, canonical map, factor and
structured arrow are unchanged. There is no proof in this file.

## Source and derived provenance

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.1, printed
pp.251–252 / one-based PDF257–258. PDF257 defines a right universal problem
by unique factorization; example 4 on PDF258 states that actual localization
of a module, viewed over its original ring, solves that problem for the full
subcategory of local modules. Registered source identifier
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These original pages were reread directly on 1 November 2026.

The source's parenthetical interpretation by a scalar inverse for each
vector is false, as shown by the published integer/rational counterexample
in `Langlands.Algebra.RenardModuleLocalization`. The imported `IsSLocal`
retains invertibility of each scalar endomorphism, which is the main
condition in the original. This statement uses that corrected interface.
The supplementary registered source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked directly on PDF18–19. Those pages do not correct the scalar
parenthesis; this is a bounded check, not an exhaustive errata claim.

The explicit full-subcategory implementation, ULift transport and
`StructuredArrow` initiality are internal derived formulations of the
source universal problem. The source makes no choice of Lean universes or
data representation. The ring and module assumptions match example 4.

## Inputs and actual objects

All declarations are in `Langlands.Renard.ModuleLocalization`. Every
component is a closed `def` with value in `Prop`. Each universally binds
`R : Type u`, `[CommRing R]`, `S : Submonoid R`, `M : Type v`,
`[AddCommGroup M]` and `[Module R M]`. The ring, source-carrier and
enlargement universes u, v and w are independent. Write κ = max u v w.

The imported constructions have the following exact meanings:

| Construction | Actual object or map |
| --- | --- |
| `LocalModuleCat.{u,κ} S` | The full subcategory of `ModuleCat.{κ} R` with the published property `IsSLocal S` |
| `localModuleInclusion S` | Its inclusion into modules over the original R |
| `raisedSource M` | `ModuleCat.of R (ULift.{max u w} M)` |
| `canonicalLocalObject S M` | The actual `ULift.{w} (LocalizedModule S M)` with its proved locality |
| `canonicalModuleMap S M` | The actual `LocalizedModule.mkLinearMap S M` transported through the explicit linear ULift equivalences |
| `canonicalFactor S M N f` | The published actual linear factor, with its source and localization-source lifts transported explicitly |
| `canonicalStructuredArrow S M` | The structured arrow of that map for the actual local-module inclusion |

Morphisms of the full subcategory are all ambient R-linear maps between
its local objects. No condition is imposed on them beyond linearity. In
particular the ambient target is an arbitrary local object N in this common
category, rather than modules over `Localization S` or a supplied
replacement localization.

## Exact assertions

`CategoricalFactorizationStatement` quantifies over every such local
object N and every ambient categorical morphism
`f : raisedSource M ⟶ N.obj`. It asserts

```text
canonicalModuleMap S M ≫
  (localModuleInclusion S).map (canonicalFactor S M N f) = f.
```

Composition has the source's right universal-arrow direction: first the
canonical map, then the image of the constructed factor.

`CategoricalFactorUniquenessStatement` quantifies over the same N and f,
and every actual local-category morphism
`g : canonicalLocalObject S M ⟶ N`. Its only added premise is the defining
factorization equation

```text
canonicalModuleMap S M ≫ (localModuleInclusion S).map g = f.
```

It concludes `g = canonicalFactor S M N f`. Together with the preceding
component this gives existence and uniqueness for every f with an identified
factor, without assuming a universal property or desired conclusion as input.

`CategoricalInitialityStatement` asserts

```text
Nonempty (StructuredArrow.IsUniversal (canonicalStructuredArrow S M)).
```

In pinned Mathlib, `StructuredArrow.IsUniversal` is an abbreviation for
initiality data in the actual structured-arrow category. Its `Nonempty`
wrapper is a proposition asserting that such data exist. This quantifies over
every structured arrow to the local-module inclusion, hence every local
target and every map from the raised source. It is not a mere uniqueness
claim among supplied factors.

`CategoricalUniversalStatements.{u,v,w}` is exactly the conjunction of
these three closed propositions. The factorization and uniqueness clauses
identify the particular imported factor. The last clause records the
categorical initiality of the particular imported structured arrow.

All denominator submonoids are retained, including those containing zero,
and the ring may be the zero ring. All modules are allowed. There is no
nontriviality, domain, faithful-action, finite-generation or dimension
assumption, no `Small` hypothesis and no shrinking of a carrier. The actual
localization has raw carrier universe max u v, explaining the explicit
raises into κ. A target at any independently specified carrier universe may
itself be raised by enlarging w. The statement concerns every target in the
resulting common ambient category; it does not silently identify independent
universes or claim that the raw localization lives in Type v.

## Intended proof and remaining scope

No proof is implemented here. A future proof should transport the already
published `factor_comp` and `factor_unique` through the explicit linear ULift
equivalences, use extensionality of the full-subcategory morphisms, and build
initiality by sending every structured arrow to its actual unique factor.
These are intended steps only. The existing linear-map universal property
does not by itself constitute an accepted proof of this categorical target.

The compatible comparison remark on PDF258 requires isomorphisms compatible
with the canonical maps; it does not assert uniqueness among all
isomorphisms. That comparison, functorial localization and adjunctions,
ring-localization example 3, the categorical polynomial-module/endomorphism
equivalence of example 5, the other examples and the rest of Appendix A
remain separate obligations. The earlier published endomorphism-localization
proofs and all existing owners are unchanged. This statement unit establishes
neither a proof nor section or book completion.
