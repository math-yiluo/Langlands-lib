# Actual separated completion of topological modules

Worker 1582 with Worker 709.

This module constructs the actual separated completion of every topological
module over a topological unital ring, its functor, canonical natural
transformation, chosen continuous linear extension maps, and explicit
comparisons with Mathlib's uniform-space completion. All declarations lie in
`Langlands.Renard.TopModuleCompletion`.

## Source and convention boundary

The motivating source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.1. The right
universal problem is defined on printed p.251 / one-based PDF257, and example 2
on printed p.252 / PDF258 motivates the completion and its canonical arrow.
The registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, with SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both pages were read directly, and PDF258 was also checked as a rendered page.

The example literally specifies continuous maps between topological vector
spaces. It does not say linear maps or fix a coefficient field. The present
construction implements the corrected convention of continuous linear maps
over a fixed topological field, with complete separated targets. The extension
to arbitrary topological unital rings and the independent universe packaging
are derived internal generalizations. These definitions do not settle the
printed reflection problem with all continuous maps. Any explanatory
rational-function obstruction remains separate from a formal theorem over a
fixed real or complex coefficient field.

The categorical universal-property proposition, uniqueness among arbitrary
competing extension morphisms, initiality and adjunction are separate successor
units. This pair supplies their actual objects and chosen maps, together with
the intrinsic continuity, functor and agreement laws needed to construct them.
It assumes no extension or universal-property certificate when selecting objects.

## Hypotheses and sizes

The main construction takes `R : Type u` with `Ring R`, `TopologicalSpace R`
and `IsTopologicalRing R`. Its ambient category is Mathlib's actual
`TopModuleCat.{v} R`; the carrier universe `v` is independent of `u`.
Morphisms are the existing continuous `R`-linear maps.

No completeness of the scalar ring, source separation, norm, local compactness,
countability, metrizability, dimension bound, commutativity or nontriviality
is imposed. Zero modules and the zero ring are allowed. A completion's canonical
map is supplied for every source; no injectivity or embedding assertion is made.

For concrete extension maps the source is any `M : Type v` and the target any
`N : Type w`, each an additive commutative group with an `R`-module structure,
topology, topological additive group structure and jointly continuous scalar
action. The universes `u`, `v` and `w` are independent. Only the target is
required to be complete for its canonical additive uniformity and separated
(`T0Space`). In fact the concrete extension reuses Mathlib under these module
hypotheses without needing the additional `IsTopologicalRing R` premise.

## Canonical uniformities and the full subcategory

`canonicalUniformSpace M` is exactly
`IsTopologicalAddGroup.rightUniformSpace M`. The equality
`canonicalUniformSpace_topology` is reflexive: its induced topology is the
original topology. For bundled ambient modules, `ambientUniformSpace`,
`ambientUniformAddGroup` and `ambientUniformConstSMul` supply this uniformity,
its `IsUniformAddGroup` structure and uniformly continuous constant scalar
actions. Their instance registrations are local to this module. Importing the
file does not replace unrelated uniform structures.

For example, a consumer working directly with a bundled module can use
`letI := ambientUniformSpace R M` and `letI := ambientUniformAddGroup R M`;
constant scalar uniform continuity is available as
`ambientUniformConstSMul R M`. The file uses these same choices consistently.
The lemma `uniformContinuous_hom` proves uniform continuity of every actual
continuous linear morphism using its underlying additive homomorphism.
`forgetToUniformSpace` retains exactly those functions.

`completeSeparatedProperty` is precisely the conjunction of `CompleteSpace`
for this chosen uniformity and `T0Space`.
`CompleteSepModuleCat` is its actual `ObjectProperty.FullSubcategory`.
`inclusion` and `inclusionFullyFaithful` give the fully faithful inclusion;
every ambient continuous linear map between selected objects is retained.
`forgetCompleteToUniformSpace` bundles these same objects and maps into
Mathlib's `CpltSepUniformSpace`. The equation `inclusion_square` states that
the two forgetful paths to `UniformSpaceCat` are definitionally equal.

## Actual completion and joint scalar continuity

`completionTopModule R M` has carrier exactly `UniformSpace.Completion M`,
formed using the source's canonical uniformity. It reuses Mathlib's existing
additive group, `R`-module, scalar multiplication, topology and uniformity.
Its joint scalar continuity is proved by `completionContinuousSMul`, rather
than supplied as an assumption.

The proof follows Worker 709's shared feasibility probe. Form the biadditive
map `(r,x) ↦ (r • x : Completion M)`, and extend it along the identity dense
inducing additive map on `R` and `Completion.toCompl` on `M`.
`IsDenseInducing.extend_Z_bilin` gives joint continuity of this extension into
the complete separated additive uniform group `Completion M`. For each fixed
scalar, `Completion.ext'` compares that extension with Mathlib's existing
scalar action. They agree on the dense original module by
`Completion.coe_smul` and the extension agreement lemma. Hence the jointly
continuous extended function is precisely the existing action.
This argument requires no completeness or separatedness of `R` or `M`.

`completion_uniformSpace_eq` uses
`IsUniformAddGroup.rightUniformSpace_eq` to identify the canonical additive
uniformity of this resulting topology with the completion's existing
uniformity. `completionObject` transfers completeness along this equality
and uses the completion's `T0Space` instance, thereby constructing the
selected full-subcategory object.

`completionMap R f` is `ContinuousLinearMap.completion f.hom`, bundled in the
full subcategory. Its underlying function is exactly
`Completion.map (f.hom : M → N)`, as `completionMap_apply` states.
`completionFunctor` proves identity and composition from
`Completion.map_id` and `Completion.map_comp` on the actual functions.

## Canonical and extension maps

`canonicalMap R M` bundles `UniformSpace.Completion.toComplL`.
`canonicalMap_apply` gives exactly `x ↦ (x : Completion M)`.
`canonicalNatTrans` assembles these maps from the identity functor to
`completionFunctor R ⋙ inclusion R`; naturality follows from
`ContinuousLinearMap.completion_apply_coe`.

For `N : CompleteSepModuleCat R` and `f : M ⟶ N.obj`,
`extensionHom R M N f` is the actual continuous linear map
`ContinuousLinearMap.fromCompletion f.hom`, bundled as a morphism from
`completionObject R M` to `N`. The equalities `extensionHom_apply` and
`extensionHom_coe` identify its value at every completion point with
`Completion.extension (f.hom : M → N.obj)` and its value at every original
point with `f.hom x`.

`concreteExtension R M N f` provides the same construction with independent
source and target universes. Its signature fixes both canonical uniformities;
it does not take an arbitrary uniform-space instance from the caller.
In particular its completeness binder is
`@CompleteSpace N (canonicalUniformSpace N)`.
`concreteExtension_toFun` is an equality of functions with
`Completion.extension (f : M → N)`, and `concreteExtension_coe` states
`concreteExtension R M N f (x : Completion M) = f x`.
No uniqueness theorem for arbitrary competing extensions is included.

## Uniform-space comparisons and field specialization

The comparison

```text
completionUniformComparison :
  completionFunctor R ⋙ forgetCompleteToUniformSpace R ≅
    forgetToUniformSpace R ⋙ UniformSpaceCat.completionFunctor
```

has components `completionUniformIso R M`. Both its forward and inverse maps
are the identity on the actual carrier `Completion M`; their uniform
continuity uses `completion_uniformSpace_eq`. The lemmas
`completionUniformIso_hom_apply` and `completionUniformIso_inv_apply`
state these identity formulas. Naturality is equality of the actual
`Completion.map` functions.

| Equality | Concrete identification |
| --- | --- |
| `canonicalMap_uniform` | Forgetting the actual canonical map and composing with the comparison gives Mathlib's `UniformSpaceCat.completionHom`. |
| `completionMap_uniform`, `completionMap_uniform_apply` | The actual completed linear morphism gives exactly the map of `UniformSpaceCat.completionFunctor`. |
| `extensionHom_uniform`, `extensionHom_uniform_apply` | Composing the comparison inverse with the forgotten actual extension gives Mathlib's `UniformSpaceCat.extensionHom`, with the same value at every completion point. |

For every `k : Type u` with `Field k`, `TopologicalSpace k` and
`IsTopologicalDivisionRing k`, `CompleteSepVectCat`,
`fieldCompletionFunctor`, `fieldCanonicalNatTrans` and `fieldExtensionHom`
are exact specializations of the same category, functor, transformation and
extension. `fieldConcreteExtension` specializes the independent-universe
concrete extension. As with the ring version, the concrete map itself only
needs the displayed continuous module structures. All formulas and comparison
laws above specialize directly to `R = k`.

The implementation uses the pinned Mathlib modules
`ModuleCat.Topology.Basic`, `IsUniformGroup.Basic`, `LinearMapCompletion`
and `Category.UniformSpace`, with the field class imported from
`Topology.Algebra.Field`. The additional packaging and comparison laws are
internal constructions, motivated by the cited example under the explicitly
corrected continuous-linear convention.
