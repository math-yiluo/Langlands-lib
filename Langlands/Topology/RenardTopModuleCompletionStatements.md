# Universal-property statements for actual topological-module completion

Worker 1582 with Worker 709 (source audit and statement design).

This pair supplies seven closed proposition definitions and their conjunction
`Langlands.Renard.TopModuleCompletion.UniversalStatements.{u,v,w}`.
They concern the actual published completion, functor, canonical maps and
chosen continuous linear extensions from
`Langlands.Topology.RenardTopModuleCompletion`. These are statements only.
Their exact proof requires a separate successor after statement publication.

## Source and convention boundary

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.1, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The right universal problem is defined on printed p.251 / one-based PDF257,
and example 2 is on printed p.252 / PDF258. Both pages were reread directly
for this statement unit, and rendered PDF258 was also inspected.

The right problem asks for a unique factor `g` satisfying `F(g) ∘ i = f`.
In Lean's composition order this is `i ≫ F.map g = f`, and the corresponding
structured arrow is initial. The completion example literally describes
continuous maps; it does not impose linearity or fix a coefficient field.
Here the corrected convention is continuous linear maps over each fixed
topological field, with complete separated targets. The arbitrary unital-ring
generalization, independent universes, explicit separation convention,
density and uniform-embedding formulation, specified adjunction and closed
conjunction are internal elaborations.

The separate `Langlands.Renard.UniformCompletion` statements use uniformly
continuous maps between uniform spaces. This pair instead uses actual
continuous linear module maps. Neither convention settles the literal printed
all-continuous-maps question. This unit gives no source counterexample and
does not identify an explanatory rational-function obstruction with a theorem
over a fixed real or complex coefficient field.

The registered older-edition supplement
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was reread on PDF18–19 for this unit. Those pages contain no correction to this
completion example. This is a bounded check of that supplement.

## Hypotheses, actual objects and uniformities

All declarations are in `Langlands.Renard.TopModuleCompletion`. Every ring
clause universally quantifies over `R : Type u` with exactly `Ring R`,
`TopologicalSpace R` and `IsTopologicalRing R`. Categorical sources are
`M : TopModuleCat.{v} R` and targets are
`N : CompleteSepModuleCat.{u,v} R`; `u` and `v` are independent.
The target category is the published full subcategory selected by
completeness for the canonical additive uniformity and `T0Space` alone.
It retains every actual continuous `R`-linear map between selected objects.
No extension, comparison or universal-property certificate selects a target.

The clauses use the published `inclusion`, `completionObject`,
`completionFunctor`, `canonicalMap`, `canonicalNatTrans` and `extensionHom`,
without parallel definitions of their objects or maps.
The completion carrier is Mathlib's actual `UniformSpace.Completion M` and
its operations are the published ones. The canonical arrow is the actual
`toComplL` map and the chosen extension is the actual `fromCompletion` map.

Where `Completion M` occurs directly, a local `letI` fixes
`UniformSpace M := canonicalUniformSpace M`. This is the published
`IsTopologicalAddGroup.rightUniformSpace M`, retaining the given topology.
The completion then uses Mathlib's existing uniformity on that actual
completion, rather than a new uniformity inferred from an unrelated caller
instance. In the concrete clause target completeness is written explicitly as
`@CompleteSpace N (canonicalUniformSpace N)`. There are no free uniform-space
instance parameters that can alter these choices. The concrete clauses also
locally derive `IsUniformAddGroup M` and `UniformContinuousConstSMul R M`
from these canonical structures, so that the completion's existing additive
group and scalar action are available; these are local constructions, not
additional premises. The uniform-embedding expressions explicitly specify
both uniform-space arguments.

The concrete source `M : Type v` and target `N : Type w` each carry exactly
`AddCommGroup`, `Module R`, `TopologicalSpace`, `IsTopologicalAddGroup` and
`ContinuousSMul R`. Only `N` has the additional canonical-uniformity
`CompleteSpace` and `T0Space` hypotheses. Thus `u`, `v` and `w` are
independent. Joint scalar continuity is required, not just continuity of
constant scalar multiplication.

There is no scalar completeness, source separation outside the embedding
implication, commutativity, nontriviality, norm, local compactness,
countability, metrizability or dimension restriction. Zero rings and zero
modules remain covered. The `T0Space` source condition occurs only as the
antecedent of the uniform-embedding conclusion; density holds for every source.

## Exact declarations

Each name below denotes a closed `Prop` definition, not a theorem. The
first five carry independent universes `u,v`; the final two and the aggregate
carry independent `u,v,w`. Their complete common hypotheses are those above.

| Declaration | Quantification and conclusion |
| --- | --- |
| `ExtensionTriangleStatement` | For every ring `R`, ambient `M`, selected `N` and actual `f : M ⟶ N.obj`, `canonicalMap R M ≫ (inclusion R).map (extensionHom R M N f) = f`. |
| `ExtensionUniqueStatement` | For the same `R,M,N,f`, every actual `g : completionObject R M ⟶ N` satisfying `canonicalMap R M ≫ (inclusion R).map g = f` equals `extensionHom R M N f`. Competing maps are unrestricted continuous linear morphisms. |
| `RightUniversalStatement` | For every `R,M`, `Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk (T := inclusion R) (canonicalMap R M)))`. This is initiality of the actual canonical arrow in the actual structured-arrow category. |
| `CanonicalAdjunctionStatement` | For every `R`, there exists `adj : completionFunctor R ⊣ inclusion R` with `adj.unit = canonicalNatTrans R`. For every `M,N,f`, `(adj.homEquiv M N).symm f = extensionHom R M N f`; for every actual `g`, `adj.homEquiv M N g = canonicalMap R M ≫ (inclusion R).map g`. The data and all equalities lie inside `Prop`; no adjunction is a premise. |
| `CanonicalMapStatement` | For every `R,M`, the function `(canonicalMap R M).hom : M → Completion M` has dense range. If `T0Space M`, this same function is a uniform embedding, from the canonical source uniformity to the completion's existing uniformity. It asserts no embedding or injectivity for a general nonseparated source. |
| `ConcreteUniversalStatement` | For every ring `R`, concrete `M,N` with exactly the displayed module hypotheses, target canonical completeness and `T0Space`, and every actual `f : M →L[R] N`, the published `concreteExtension R M N f` agrees with `f` on every canonical image of `x : M`. Every actual `g : Completion M →L[R] N` with this agreement equals that chosen extension. An explicit `∃! g` with the agreement property also records the full existence and uniqueness conclusion. |
| `FieldSpecializationStatement` | For every `k : Type u` with exactly `Field k`, `TopologicalSpace k` and `IsTopologicalDivisionRing k`, the same six conclusions hold, using the published field aliases as detailed below. |

`UniversalStatements` conjoins, in order, `ExtensionTriangleStatement`,
`ExtensionUniqueStatement`, `RightUniversalStatement`,
`CanonicalAdjunctionStatement`, `CanonicalMapStatement`,
`ConcreteUniversalStatement` and `FieldSpecializationStatement`.
It has no outer mathematical premises.

## Exact field specialization and implementation boundary

`FieldSpecializationStatement` quantifies over every topological field with
the three field hypotheses above. Its categorical targets are the published
`CompleteSepVectCat.{u,v} k`. It combines the chosen triangle and arbitrary
competitor uniqueness using `fieldExtensionHom k M N f`; initiality uses
the same actual `canonicalMap k M` for `inclusion k`.
It existentially asserts the adjunction
`fieldCompletionFunctor k ⊣ inclusion k`, specifies its unit as exactly
`fieldCanonicalNatTrans k`, and specifies both Hom formulas, using
`fieldExtensionHom` for the inverse. It also states the same density and
conditional embedding conclusions for `canonicalMap k M`.
Its concrete clause uses the published `fieldConcreteExtension`, with
`M : Type v` and `N : Type w`, the same additive, topological and continuous
module structures, and only target canonical completeness and `T0Space`.
It asserts chosen agreement, uniqueness among all continuous linear
competitors and the explicit `∃!` conclusion.
Every field alias unfolds to the corresponding ring construction; no
alternative completion, functor, canonical arrow or extension is introduced.

`StructuredArrow.IsUniversal` and `Adjunction` carry data in Mathlib.
Initiality is therefore wrapped in `Nonempty`, and adjunction data are
existentially quantified within `Prop`. The directions of `homEquiv` are
fixed: its forward direction is from completion-to-target morphisms to
source-to-included-target morphisms, and its inverse is the chosen extension.

The implementation imports the published construction and Mathlib's
`CategoryTheory.Adjunction.Basic` and
`CategoryTheory.Comma.StructuredArrow.Basic` directly. This pair constructs
no adjunction data and proves none of its propositions. Their exact proof
is the next mathematical obligation after independent statement acceptance
and publication. The uniformly continuous construction and literal printed
continuous-map question retain their separate owners and scope.
