# Global sections twisted by the dual of a line bundle from the base

This internal module attaches to a module map out of a pulled back line bundle
a global section of a twisted bundle. It also computes the pullbacks of such
sections along arbitrary morphisms. All schemes lie in one arbitrary universe
`u`. Declarations are in the namespace `Langlands.AlgebraicGeometry.LinearSystem`.

## Tensor helpers

- `tensorMap_zero_id`: if `B` is locally free of rank one, then
  `tensorMap (0 : A ⟶ A') (𝟙 B) = 0`. The proof uses the published
  `Modules.tensorBy_isEquivalence`. Tensoring with `B` is an equivalence, so
  it preserves zero morphisms.
- `isIso_tensorMap` (instance): the tensor of two isomorphisms is an
  isomorphism.
- `pullback_map_tensorMap_id`: for `f : T ⟶ X`, the pullback of
  `tensorMap α (𝟙 B)` is `tensorMap (f^* α) (𝟙 _)`, conjugated by the
  published canonical comparison `pullbackTensorComparisonApp`. That comparison
  is an isomorphism by the published instance `pullbackTensorComparisonApp_isIso`.
  The proof uses the published naturality `pullbackTensorComparisonApp_naturality`.

## Twisted sections

Let `p : X ⟶ S`, `L` a module sheaf on `X` and `Λ` a line bundle on `S`. Write
`Λ^∨` for the published internal dual `Langlands.Scheme.Modules.dual Λ.obj`.

- `lineCoevaluation Λ : 𝒪_S ⟶ Λ ⊗ Λ^∨` is the inverse of the published
  evaluation `dualTensorEval Λ.obj`. That evaluation is an isomorphism by the
  published `isIso_dualTensorEval`.
- `pulledCoevaluation p Λ : 𝒪_X ⟶ p^*Λ ⊗ p^*Λ^∨` is the composite of three
  isomorphisms: the inverse of `pullbackUnitIso p`, the pullback of the
  coevaluation, and the canonical tensor comparison. It is an isomorphism.
- `twistedHom p Λ α`, for `α : p^*Λ ⟶ L`, is
  `pulledCoevaluation p Λ ≫ tensorMap α (𝟙 _) : 𝒪_X ⟶ L ⊗ p^*Λ^∨`.
- `twistedSection p Λ α` is its value at `1` on global sections, a global
  section of `L ⊗ p^*Λ^∨`. Its section morphism is `twistedHom p Λ α`.

When `L` is a line bundle on `X`, `L ⊗ p^*Λ^∨` is the twist of `L` by the
line bundle `(p^*Λ)^∨` from the base. Locally, `twistedSection p Λ α` is
"`α` divided by a local generator of `p^*Λ`".

## Pullback along a morphism `f : T ⟶ X`

- `sectionHom_pullbackSection_twistedSection` writes the section morphism of
  `pullbackSection f _ (twistedSection p Λ α)` as a composite of isomorphisms
  with `tensorMap (f^* α) (𝟙 _)`.
- `pullbackSection_twistedSection_congr`: the pulled back section depends only
  on `f^* α`.
- `pullbackSection_twistedSection_eq_zero`: if `f^* α = 0`, the pulled back
  section is zero. This uses `tensorMap_zero_id` for the line bundle
  `f^* p^* Λ^∨`.
- `trivializationOpen_pullbackSection_twistedSection`: if `f^* α` is an
  isomorphism, the pulled back section generates its bundle everywhere (its
  trivialization open is `⊤`). Its section morphism is then an isomorphism, and
  the published `trivializationOpen_eq_top_of_isIso` applies.

## Provenance

These are standard manipulations with a line bundle and its dual. They are
used in `FrameEmbeddingReduction` to build the sections `τ_j` of
`L³ ⊗ π^* Λ^{-1}` described in the Markdown of
`FrameEmbeddingExistenceStatement`. No literature statement is formalized
here.
