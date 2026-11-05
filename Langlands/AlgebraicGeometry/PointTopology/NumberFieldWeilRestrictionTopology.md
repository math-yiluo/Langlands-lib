# Actual all-upper-place Weil point homeomorphisms for number fields

Author: Worker 208.

This module specializes the completed-tensor Weil point homeomorphism to all
actual upper places of a number-field extension. It implements the
field-valued local comparison in Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 4.2, printed page 10.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Conrad's example treats finite extensions of global fields in both
characteristics. This module gives the number-field specialization of the
local step. The function-field realization, integral-model comparison, and
global adelic homeomorphism remain separate obligations.

## Inputs and actual geometric object

Let `K` and `L` be number fields in one arbitrary common universe, with an
actual `K`-algebra structure on `L`. The finite-dimensional and projective
`K`-module structures on `L` follow from these inputs; no separate extension
degree, separability, or Galois premise is required.

Let `Y` be an actual scheme over `Spec L`, locally of finite type, and let

```text
j : Y.left ⟶ ProjectiveSpace L n
```

be an actual immersion satisfying
`j ≫ projectiveSpaceToSpec L n = Y.hom`. The general comparison derives
separatedness and finite-set affine neighborhoods from this immersion.
The `K`-scheme in each source point set is the actual independently glued
`affineChartWeilRestriction K L Y`. There is no assumed representing
equivalence or local comparison in the inputs.

## All finite upper places

For any actual height-one prime `v` of the ring of integers of `K`,
`finitePlaceWeilRestrictionPointHomeomorph` constructs

```text
RingPoint K (affineChartWeilRestriction K L Y) (v.adicCompletion K)
  ≃ₜ (∀ q : FinitePlacesAbove L v, RingPoint L Y (q.1.adicCompletion L)).
```

`FinitePlacesAbove L v` is the subtype of all actual height-one primes of
the ring of integers of `L` lying over `v`; it is finite by the existing
prime-above results. Each `q.1.adicCompletion L` has its original completion
topology and its original `L`-algebra structure.

The extension of local scalar fields is the scoped `FiniteExtension`
algebra structure, constructed from the actual continuous completion
embedding `completionMap`. Its degree is already proved finite. The private
helper `finitePlaceFactorIsModuleTopology` equips the lower completion with
the nontrivially normed-field structure associated to its original valuation,
and applies `isModuleTopologyOfFiniteDimensional`. Completeness, Hausdorffness,
and continuous scalar multiplication are the existing completion instances.
Thus the module-topology premise of the general comparison is derived.

The algebra decomposition is `finitePlaceTensorEquiv K L v`, namely the
canonical `finiteTensorMap v` packaged as an algebra equivalence using the
published unconditional `completedTensorComparison` proof. Its proved
`finitePlaceTensorEquiv_one_tmul` law supplies the original right `L`-factor
compatibility. There is no assumed tensor bijectivity or tensor equivalence
in this specialized definition.

## All infinite upper places

For any actual infinite place `v` of `K`,
`infinitePlaceWeilRestrictionPointHomeomorph` constructs

```text
RingPoint K (affineChartWeilRestriction K L Y) v.Completion
  ≃ₜ (∀ q : InfinitePlacesAbove L v, RingPoint L Y q.1.Completion).
```

`InfinitePlacesAbove L v` contains all actual infinite places of `L` lying
over `v`. Both real and complex completions occur with their existing
topologies and completion embeddings; no choice of a real or complex
presentation is an input.

The scoped `NumberField.LiesOver` and `InfiniteExtension` instances provide
the actual local algebra, continuous scalar action, and proved finite local
degree. The private helper `infinitePlaceFactorIsModuleTopology` uses
`infiniteCompletionNontriviallyNormedField`, which preserves the original
norm and topology, and applies the same finite-dimensional module-topology
theorem.

The actual coefficient equivalence is the existing `infiniteTensorEquiv v`;
its right `L`-factor law is `infiniteTensorMap_one_tmul v`. The canonical
tensor map and its proved bijectivity are already implemented, so no
arithmetic comparison is assumed here.

## Independent topologies and original component maps

In each definition, the source has its own `schemePointTopology` and every
target factor has its own `schemePointTopology`; the target is their product.
These topologies are not transported through the comparison. The construction
calls `projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph` with
the actual arithmetic equivalence and the derived module-topology instances.
It therefore uses the previously constructed tensor, coefficient, finite-product,
local Weil, factor-target, and ordinary base-change homeomorphisms.

The two `_counit` theorems identify every component with

```text
completedTensorWeilRestrictionFactorTestMap ... q ≫
  affineChartWeilRestrictionComparison K L Y (ringTest K lowerCompletion) p.
```

The factor test map is the actual map
`Spec upperCompletion → Spec lowerCompletion ×[Spec K] Spec L`.
It is constructed from the original completed-tensor decomposition,
coordinate evaluation at `q`, and the canonical spectrum-of-tensor pullback
isomorphism. The right-factor law ensures the map has the original
`L`-structure. The comparison on the right is the original Weil counit.
Both theorems are direct specializations of the generic proved counit
identity; neither comparison is redefined.

The point homeomorphisms consequently realize the original local set map for
all upper places. They assert neither the integral-point homeomorphism nor
the passage from local products to the adelic direct limit.
