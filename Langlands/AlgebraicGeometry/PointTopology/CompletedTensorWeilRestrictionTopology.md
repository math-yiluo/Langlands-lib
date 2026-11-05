# Completed-tensor decomposition of actual Weil point topologies

Author: Worker 208.

This construction implements the local product comparison used in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Example 4.2, printed page 10. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Conrad identifies the completed tensor algebra of a finite global-field
extension with the product of the completions at all upper places, decomposes
the resulting Weil scheme, and applies the local finite-extension
homeomorphism to each factor. This module composes those scheme and topology
comparisons for a supplied tensor decomposition. It also identifies the
resulting component maps with the original Weil counit. Its arbitrary-ring
scope is a derived generalization of that step; the arithmetic specializations
and the global adelic comparison are separate obligations.

## Inputs and point spaces

All rings and indices inhabit the same arbitrary universe. Let `A`, `B`, and
`C` be commutative rings, with `A`-algebra structures on `B` and `C`. Assume
that `B` is finite and projective as an `A`-module. Let `ι` be a finite index
type and let `D i` be commutative rings equipped with both `C`- and `B`-algebra
structures. Assume that each `D i` is finite and projective as a `C`-module.
The supplied algebraic decomposition is

```text
e : C ⊗[A] B ≃ₐ[C] (∀ i, D i).
```

Its right tensor factor must preserve the original `B`-structures:

```text
he : ∀ b i, e (1 ⊗ₜ[A] b) i = algebraMap B (D i) b.
```

Let `Y` be an actual scheme over `Spec B`, locally of finite type. The general
construction assumes that `Y → Spec B` is separated and that every finite set
of points of `Y` lies in an affine open, expressed by
`HasFiniteAffineNeighborhoods Y.left`.

The value ring `C` and every `D i` carry their own topological-ring structures.
They are local rings with `IsOpenUnits`: the units form an open set and
inversion is continuous there. The topology on `D i` must be its module
topology over `C`, expressed by `IsModuleTopology C (D i)`.

`completedTensorWeilRestrictionPointHomeomorph` constructs

```text
RingPoint A (affineChartWeilRestriction A B Y) C
  ≃ₜ (∀ i, RingPoint B Y (D i)).
```

The source is the actual set of morphisms over `Spec A` from `Spec C` to the
independently constructed affine-chart Weil scheme. Each target factor is
the actual set of morphisms over `Spec B` from `Spec (D i)` to `Y`. Both sides
use their previously defined `schemePointTopology`; the product on the right
has the product topology. Neither topology is defined by transport through
this homeomorphism.

No topology on `A`, `B`, or the tensor algebra is required. Continuity of `e`
is not an assumption. The value rings need not be fields, complete, or of
characteristic zero. Locality, the open-unit condition, finite projectivity,
and the module-topology premise remain explicit.

## Construction and intermediate geometry

Put `E = C ⊗[A] B`, `Z = Y ×[Spec B] Spec E`, and let `W` be the actual
pullback of `Z` along `Spec e : Spec (∀ i, D i) → Spec E`.

The construction composes these existing homeomorphisms:

1. Tensor base change identifies the `C`-points of the original `B/A` Weil
   scheme with the `C`-points of the actual `E/C` Weil scheme of `Z`.
2. The coefficient-isomorphism comparison replaces `E` with `∀ i, D i`
   and replaces `Z` with its actual pullback `W`.
3. The finite-product Weil comparison gives the product of the `C`-points of
   the actual `D i/C` Weil schemes of the corresponding factor targets.
4. The local Weil comparison gives the `D i`-points of each factor target.
5. `tensorCoefficientFactorTargetIso` identifies that factor target with
   `Y ×[Spec B] Spec (D i)`, using `he`.
6. The inverse of the ordinary base-change point homeomorphism returns the
   original `B`-scheme's `D i`-points.

Locally finite-type and separated morphisms are preserved by each of the
actual pullbacks, so the local intermediate instances follow by base change.
The finite-set affine-neighborhood property is derived at the tensor,
coefficient, and factor stages by the existing affine inverse-image lemmas.
There are no extra geometric premises on these intermediate schemes.

The tensor algebra is finite and projective over `C` by base change from
`B/A`; the product-algebra instances used by the product comparison come
from finiteness of `ι` and the given finite-projective factor modules.
The construction does not require any of these algebras to be local.

## Original counit and exact component maps

`completedTensorWeilRestrictionFactorTestMap` is defined before the finiteness,
geometry, and topology hypotheses. For each `i`, it is the actual map over
`Spec B`

```text
Spec (D i) → Spec C ×[Spec A] Spec B
```

whose underlying scheme map is the composite of `Spec` of coordinate
evaluation, `Spec e`, and the inverse of `pullbackSpecIso A C B`. Its
compatibility with the original `B`-structure follows from `he`.

`completedTensorWeilRestrictionPointHomeomorph_apply` gives the literal
component of the composite homeomorphism in terms of coefficient transport,
the canonical product projection, the local factor comparison, the
factor-target isomorphism, and inverse ordinary base change.

`completedTensorWeilRestrictionPointHomeomorph_counit` proves the more
intrinsic identity

```text
homeomorph p i =
  completedTensorWeilRestrictionFactorTestMap A B C D e he i ≫
    affineChartWeilRestrictionComparison A B Y (ringTest A C) p.
```

Here the comparison on the right is the original Weil scheme's counit
comparison, already constructed independently of the homeomorphism.
The proof first expands the component formula. It uses the projection
identities of the factor-target isomorphism and the product, coefficient,
and tensor comparisons to reduce to that original counit. Naturality of
the counit then reduces the remaining equality to the two projections of
the original test pullback. The private test-isomorphism lemmas establish
these projection equalities from the corresponding pullback equations.
Thus the final homeomorphism has the original set map, rather than a map
specified only by an unnamed choice of bijection.

## Projective-immersion specialization

`projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph` assumes
an actual immersion `j : Y.left ⟶ ProjectiveSpace B n` with
`j ≫ projectiveSpaceToSpec B n = Y.hom`. It derives separatedness and the
finite-set affine-neighborhood property using the existing projective-space
results, and calls the general construction. Locally finite type remains
an explicit hypothesis on `Y`.

Its `_counit` theorem retains exactly the original-counit formula above.
No separate separatedness or affine-neighborhood premise occurs in this
specialized definition or its formula.

## Scope

This is a construction and compatibility unit for the local completed-tensor
step. The supplied decomposition and finite-projective module hypotheses
are premises of the general result. Instantiating them for all actual upper
places, including function fields, is separate work. Integral models,
comparison of their local integral points, passage to adelic direct limits,
and the rest of Conrad's five sections are not established by this module.
