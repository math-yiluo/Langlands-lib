# Morphism presheaves and precomposition

This internal construction compares two ways of restricting the full morphism
presheaf of a category-valued pseudofunctor. It derives from the definitions in
Mathlib, rather than translating an external existence theorem.

Let `G : C ⥤ D`, let `F` be a pseudofunctor from `LocallyDiscrete Dᵒᵖ` to
`Cat`, and let `M` and `N` be objects of its fibre over `G.obj S`.
`Langlands.CategoryTheory.presheafHomPrecompositionIso` is a natural
isomorphism on the entire category `(Over S)ᵒᵖ`:

```text
(G.op.toPseudofunctor.comp F).presheafHom M N
  ≅ (Over.post G).op ⋙ F.presheafHom M N.
```

Both presheaves evaluate at `p : T → S` as morphisms between the pullbacks of
`M` and `N` along `G.map p`. Each component of the comparison is the identity
isomorphism on this same morphism type. The source and target categories have
independent object and morphism universes; the value universe is the morphism
universe of the fibres of `F`.

Naturality concerns the full coherent restrictions, not just an isolated
pullback operation. The implemented proof first expresses naturality using
Mathlib's `pullHom`. It then unfolds pseudofunctor composition, the locally
discrete lift of `G.op`, and the flexible composition comparison `mapComp'`.
The extra comparison isomorphisms supplied by the ordinary functor are equality
isomorphisms. Combining their images under `F.map₂` reduces the two restrictions
to the same composition comparisons and the same mapped morphism. The final
equality uses equality-morphism composition and proof irrelevance.

No descent, sheaf condition, representability, or geometric hypothesis is used
or asserted. This is a coherence comparison for arbitrary categories and
arbitrary category-valued pseudofunctors.
