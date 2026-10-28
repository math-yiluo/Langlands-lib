# Open restriction commutes with the sheaf tensor product: statement

This module defines the proposition

```text
RestrictTensorComparisonStatement (X : AlgebraicGeometry.Scheme.{u}) : Prop
```

in namespace `Langlands.Scheme.Modules`, for an arbitrary universe `u`. It
imports `Langlands.AlgebraicGeometry.Modules.RestrictTensor`, which defines the
comparison

```text
restrictTensorHom U M N :
  tensorObj (M.restrict U.ι) (N.restrict U.ι) ⟶ (tensorObj M N).restrict U.ι
```

for an open `U : X.Opens` and module sheaves `M N : X.Modules`. The
ingredients are the following.

- `tensorObj` is the explicit sheafified sectionwise tensor product from
  `Langlands.AlgebraicGeometry.Modules.Tensor`. It is not the localized
  monoidal tensor `⊗` on `X.Modules`.
- `tensorSheafifyUnit M N : M.val ⊗ N.val ⟶ (tensorObj M N).val`, from
  `Langlands.AlgebraicGeometry.Modules.PullbackTensor`, is the unit of the
  sheafification adjunction at the sectionwise tensor presheaf. It sends a
  pure tensor of sections to its class in the sheaf tensor.
- `restrict` is Mathlib's `AlgebraicGeometry.Scheme.Modules.restrict` along
  the open immersion `U.ι : U.toScheme ⟶ X`. Mathlib identifies the
  restriction functor with pullback along `U.ι`
  (`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`), but the
  statement does not use that identification.

## Statement

The proposition says that for every open `U : X.Opens` and all module sheaves
`M N : X.Modules`, both of the following hold.

1. `IsIso (restrictTensorHom U M N)`. The comparison from the tensor product
   of the restrictions to the restriction of the tensor product is an
   isomorphism of sheaves of modules on `U`.
2. For every open `V : U.toScheme.Opens` and sections
   `m : (M.restrict U.ι).val.obj (op V)` and
   `n : (N.restrict U.ι).val.obj (op V)`,

   ```text
   ((restrictTensorHom U M N).val.app (op V)).hom
       (((tensorSheafifyUnit (M.restrict U.ι) (N.restrict U.ι)).app (op V)).hom
         (m ⊗ₜ[U.toScheme.presheaf.obj (op V)] n))
     = ((tensorSheafifyUnit M N).app (op (U.ι ''ᵁ V))).hom
         (m ⊗ₜ[X.presheaf.obj (op (U.ι ''ᵁ V))] n).
   ```

   By definition of `restrict`, `m` and `n` are sections of `M` and `N` over
   the open `U.ι ''ᵁ V` of `X`, with scalars restricted from
   `𝒪_X(U.ι ''ᵁ V)` to `𝒪_U(V)`. The left side takes the sheafified pure
   tensor of `m` and `n` over `𝒪_U(V)` and applies the comparison at `V`. The
   right side is the sheafified pure tensor of the same sections over
   `𝒪_X(U.ι ''ᵁ V)`. Both sides are sections of `tensorObj M N` over
   `U.ι ''ᵁ V`, since that is the value of `(tensorObj M N).restrict U.ι` at
   `V`. So the comparison sends `m ⊗ n` to `m ⊗ n`.

The scheme `X` and the universe `u` are arbitrary. There are no affine,
quasi-coherent, finiteness or other hypotheses on `X`, `U`, `M` or `N`.
Clause 2 is stated for arbitrary sections; it does not say that pure tensors
generate the sheaf tensor.

## Provenance

[Stacks Project, Section 17.16 (tag 01CA)](https://stacks.math.columbia.edu/tag/01CA)
defines the tensor product of two sheaves of modules as the sheafification of
the presheaf `V ↦ F(V) ⊗_{𝒪_X(V)} G(V)`.
[Lemma 17.16.4 (tag 01CD)](https://stacks.math.columbia.edu/tag/01CD) says
that for a morphism of ringed spaces `f`, `f^*(F ⊗ G) = f^*F ⊗ f^*G`,
functorially in `F` and `G`. For an open immersion, pullback is restriction to
the open. Clause 1 is the case of this lemma for the open immersions `U.ι`,
asserted for the explicit canonical map `restrictTensorHom`. The source omits
the proof of Lemma 17.16.4 and does not write down a comparison map, so the
choice of this map is internal. It is the map built in `RestrictTensor`:
sectionwise `m ⊗ n ↦ m ⊗ n` on the presheaf tensors, followed by
sheafification. Clause 2 is internal too. It records this sectionwise formula
for the sheafified map, which is how `restrictTensorHom` is built.

The retained source is `stacks-module-tensor-products-2026-10-21`, *Stacks
Project - Tensor products of sheaves of modules (HTML snapshot 2026-10-21)*,
SHA256 `825127394e5828c3a56f5134b8823afba20547d7ba5173f624b2f9556a058e34`.
On 2026-10-28 the current Section 17.16 page was byte-identical to this
snapshot. The current tag 01CD page has no comments. The seven comments on
Section 17.16 concern the definition of bilinear maps, the order of two
lemmas, and a 2023 remark on a proof strategy for 01CD, which the project left
as is in 2024. None corrects the definition or Lemma 17.16.4.

The proposition is narrower than the source lemma. It covers only open
immersions, not arbitrary morphisms of ringed spaces. It states neither
naturality in `M` and `N` nor any compatibility with associators, unitors or
the localized monoidal tensor `⊗`. It does not state or use the general
pullback/tensor comparison `pullbackTensorComparisonApp` or its statement
`pullbackTensorComparisonIsIsoStatement`.

Worker 207 wrote the draft of this module. Worker 317 checked it against the
published definitions and the source, and revised this Markdown.

This module provides no proof, no `IsIso` instance and no helper theorem. The
proof is a separate successor task.
