# The open-restriction comparison for the sheaf tensor product

This module defines, for an open `U : X.Opens` of a scheme `X : Scheme.{u}`
and module sheaves `M N : X.Modules`, the canonical comparison morphism

```text
restrictTensorHom U M N :
  tensorObj (M.restrict U.ι) (N.restrict U.ι) ⟶ (tensorObj M N).restrict U.ι
```

from the tensor product of the restrictions to the restriction of the tensor
product. Here `tensorObj` is the explicit sheafified sectionwise tensor
product from `Langlands.AlgebraicGeometry.Modules.Tensor`, not the localized
monoidal tensor `⊗` on `X.Modules`. `restrict` is Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrict` along the open immersion
`U.ι : U.toScheme ⟶ X`. The module imports `Langlands.AlgebraicGeometry.Modules.Tensor`,
`Langlands.AlgebraicGeometry.Modules.PullbackTensor` and
`Langlands.AlgebraicGeometry.Modules.TensorMonoidal`. All declarations are in
namespace `Langlands.Scheme.Modules`.

This module contains only definitions. It does not prove that the comparison is
an isomorphism, or compute it on sections. Both facts belong to the separate statement successor
`RestrictTensorComparisonStatement` in
`Langlands.AlgebraicGeometry.Modules.RestrictTensorStatement` and its proof task.

## Provenance

[Stacks Project, Section 17.16 (tag 01CA)](https://stacks.math.columbia.edu/tag/01CA), defines the tensor product of two
sheaves of modules as the sheafification of the presheaf
`V ↦ F(V) ⊗_{𝒪_X(V)} G(V)`. [Lemma 17.16.4 (tag 01CD)](https://stacks.math.columbia.edu/tag/01CD) says that pullback along
a morphism of ringed spaces commutes with tensor products. For an open
immersion, pullback is restriction to the open. The retained source is
`stacks-module-tensor-products-2026-10-21`, *Stacks Project - Tensor products
of sheaves of modules (HTML snapshot 2026-10-21)*, SHA256
`825127394e5828c3a56f5134b8823afba20547d7ba5173f624b2f9556a058e34`. The source
gives no proof of Lemma 17.16.4, and it does not write down a comparison map.

Worker 207 authored the reused draft of these definitions. Worker 5 checked
the interfaces, source correspondence and documentation. The construction
below is internal. It writes down the canonical map in the
direction `M|_U ⊗ N|_U ⟶ (M ⊗ N)|_U`, defined sectionwise on the presheaf
tensor and then extended by the universal property of sheafification. It does
not use the general pullback/tensor comparison `pullbackTensorComparisonApp`
from `PullbackTensor`. It covers only restriction along the open immersions
`U.ι`.

The current Stacks pages and their comment threads were checked on
2026-10-28. Tag 01CD has no comments; Section 17.16 has seven, including a
2023 comment about proof strategy for 01CD and a 2024 reply leaving its
proof omitted. No correction to the cited definition or pullback statement
was found. No source-specific project errata note was present.

## Definitions

- `restrictRingMap U` is the morphism of ring presheaves
  `U.toScheme.ringCatSheaf.obj ⟶ U.ι.opensFunctor.op ⋙ X.ringCatSheaf.obj`
  with components `(U.ι.appIso V).inv`, viewed in `RingCat`. Mathlib's
  restriction functor restricts scalars along this map, so
  `(M.restrict U.ι).val` is the pushforward of `M.val` along it. The value of
  `M.restrict U.ι` on `V : U.toScheme.Opens` is `M(U.ι ''ᵁ V)`.
- `restrictTensorLift U M N` is the presheaf-of-modules map

  ```text
  (M.restrict U.ι).val ⊗ (N.restrict U.ι).val ⟶
    pushforward (restrictRingMap U) (M.val ⊗ N.val).
  ```

  Its component at `V` is the canonical map
  `M(ι V) ⊗_{𝒪_U(V)} N(ι V) → M(ι V) ⊗_{𝒪_X(ι V)} N(ι V)`,
  `m ⊗ n ↦ m ⊗ n`, where `ι V = U.ι ''ᵁ V`. In Lean this is
  `restrictScalarsTensorLift (U.ι.appIso V).inv.hom (𝟙 _)`, with
  `restrictScalarsTensorLift` from `PullbackTensor`. Naturality is checked on
  pure tensors and holds by `rfl`.
- `restrictTensorPresheafHom U M N` is `restrictTensorLift U M N` followed by
  the pushforward of the sheafification unit `tensorSheafifyUnit M N`. Its
  target is the presheaf `((tensorObj M N).restrict U.ι).val`.
- `restrictTensorHom U M N` is the transpose of `restrictTensorPresheafHom U M N`
  under `tensorHomEquiv`, which is the sheafification adjunction on `U`.

## Scope

The module defines no inverse and no naturality in `M` and `N`. It states no
compatibility with associators, unitors or the localized monoidal structure.
