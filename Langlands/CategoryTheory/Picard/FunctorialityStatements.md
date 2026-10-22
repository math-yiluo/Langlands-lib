# Functoriality statements for the categorical Picard group

This module defines three proposition targets in
`Langlands.CategoryTheory.PicardGroup`. They concern the categorical Picard
group and its induced additive homomorphism from
`Langlands.CategoryTheory.Picard.Basic`.

For a braided monoidal category `C`, `PicardGroup C` is the additive type tag
on the group of units of the monoid of isomorphism classes `Skeleton C`.
Tensor product supplies the monoid operation, and braiding makes it commutative.
A strong monoidal functor `F : C ⥤ D`, represented by Mathlib's
`Functor.Monoidal` instance, induces `map F : PicardGroup C →+ PicardGroup D`.
The functor is not required to preserve the chosen braidings.

Every category has its own independent object universe and morphism universe.
All categories in the statements carry `Category`, `MonoidalCategory`, and
`BraidedCategory` instances. The equalities below are equalities of additive
homomorphisms.

- `MapIdentityStatement C` states
  `map (𝟭 C) = AddMonoidHom.id (PicardGroup C)`, using the canonical strong
  monoidal structure on the identity functor.
- `MapCompositionStatement F G` states
  `map (F ⋙ G) = (map G).comp (map F)` for strong monoidal functors
  `F : C ⥤ D` and `G : D ⥤ E`. The composite uses Mathlib's induced strong
  monoidal structure; the order on the right first applies `map F`, then `map G`.
- `MapIsoStatement F G` states that every ordinary natural isomorphism
  `F ≅ G` between strong monoidal functors `C ⥤ D` gives
  `map F = map G`. No compatibility between this natural isomorphism and the
  monoidal structures is assumed.

These are internally derived categorical functoriality targets. Their provenance
is the object-class construction underlying Mathlib's `Skeleton.monoidHom`,
followed by the induced homomorphism on units and the additive type tag.
Identity and composite functors act on object classes as their names indicate.
For the natural-isomorphism target, the component at each object identifies the
two image objects up to isomorphism, which is the equivalence relation defining
the skeleton. This explains why ordinary natural isomorphism is sufficient.

The module contains proposition definitions only. It does not prove these
targets or assert a scheme-specific Picard construction.
