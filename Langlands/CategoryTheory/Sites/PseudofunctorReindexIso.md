# Strong transformations of reindexed pseudofunctors from natural isomorphisms

Namespace: `Langlands.CategoryTheory.PseudofunctorReindexIso`.

This is internal categorical infrastructure derived from Mathlib's
pseudofunctor API (in particular the strict-source associativity lemmas in
`Mathlib/CategoryTheory/Bicategory/Strict/Pseudofunctor.lean`) and the
published `StackPullback` module. It introduces no new literature assertion.

## Building strong transformations on objects

`catStrongTrans` constructs a `Pseudofunctor.StrongTrans F G` between
category-valued pseudofunctors on `LocallyDiscrete B₀` from component functors
`A a`, naturality isomorphisms `n h : F(h) ⋙ A b ≅ A a ⋙ G(h)`, and the two
coherence identities (unit `hi` and composition `hc`) checked on objects. It
follows the private helper of the published `Picard.ModuleComparison` module.

## Reindexing lemmas

For `G : C ⥤ E` and `P : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat`, write
`reindex G P = G.op.toPseudofunctor.comp P` (published `StackPullback`).

- `mapComp_reindex` rewrites the composition comparison of `reindex G P` at
  `h₁.op, h₂.op` as `P.mapComp'` at the image arrows.
- `mapId_reindex` rewrites the identity comparison as `P.mapId'` at
  `G.map (𝟙 X)`; `mapId_reindex_reindex` does the same for a twice reindexed
  pseudofunctor.
- `op_toLoc_comp_eq` turns an equality of composites in `E` into the
  corresponding equality in `LocallyDiscrete Eᵒᵖ`.

## The strong transformation

Fix functors `G₁ : C ⥤ E`, `Φ : C ⥤ D`, `G₂ : D ⥤ E` and a natural
isomorphism `θ : G₁ ≅ Φ ⋙ G₂`.

- `component P θ X` is pullback along `θ.inv.app X : G₂ (Φ X) ⟶ G₁ X`.
- `inv_comm` is the naturality square of `θ.inv`.
- `naturalityIso P θ h`, for `h : Y ⟶ X`, is the composite of the inverse
  composition comparison for `(G₁ h, θ.inv.app Y)` with the composition
  comparison for `(θ.inv.app X, G₂ (Φ h))`, both through the common composite
  `θ.inv.app Y ≫ G₁.map h`.
- `naturalityIso_comp` is the oplax functoriality identity. After the
  reindexing rewrites it is an identity between composites of
  `P.mapComp'`; it follows from three applications of Mathlib's
  associativity lemmas `mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom`,
  `mapComp'₀₂₃_hom` and `mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom`.
- `mapComp'_mapId'_aux` and `naturalityIso_id` give the unit identity, using
  `mapComp'_id_comp` and `mapComp'_comp_id` after substituting identities.
- `strongTrans P θ` is the strong transformation
  `reindex G₁ P ⟶ reindex Φ (reindex G₂ P)` with these components and
  naturality isomorphisms; `strongTrans_app` records its components.
- `mapIsoEquivalence P t` is the equivalence of fibres given by pullback along
  an isomorphism `t` of `E`, with unit and counit built from the composition
  and identity comparisons (Mathlib's `Equivalence.mk` adjointifies them).
- `strongTransFullyFaithful` shows that every component of `strongTrans P θ`
  is fully faithful, because it is the functor of such an equivalence.

With the published `PseudofunctorPointFiberTransport.presheafIso`, this gives
isomorphisms of entire point-fibre presheaves. The geometric application
compares the relative Picard pseudofunctors of a scheme and of its base change.
