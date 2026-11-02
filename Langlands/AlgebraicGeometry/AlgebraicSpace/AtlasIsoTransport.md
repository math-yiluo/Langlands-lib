# Scheme atlas transport along a presheaf isomorphism

Author: Worker 509.

This internal module derives transport lemmas from the published
`AlgebraicSpace.Basic` and `AlgebraicSpace.RelativeHelpers` interfaces and
Mathlib's relatively representable morphism properties. It introduces no
existence theorem for a quotient, a Picard sheaf, or a scheme atlas.

For an arbitrary base scheme `S : Scheme.{u}`, all presheaves are the full
functors `(Over S)ᵒᵖ ⥤ Type (u+1)`, and every isomorphism is a natural
isomorphism on that entire category.

`IsSurjective.comp_iso` shows that a geometrically surjective representable
transformation remains so after composition with a presheaf isomorphism.
The proof applies isomorphism invariance of the relative scheme-morphism
property `Surjective`, pulled back to `Over S`. Its meaning includes
representability and surjectivity of every represented scheme projection,
as in the original definition; it is not merely surjectivity on sections.

`hasRepresentableDiagonal_of_iso` transports scheme representability of
the diagonal from `F` to `G` along `e : F ≅ G`. The proof writes the
diagonal of `G` as `e.inv`, followed by the diagonal of `F`, followed by
the product isomorphism from `F × F` to `G × G`. Relative
representability is invariant under composition with these isomorphisms.

`exists_locallyFiniteType_atlas_of_iso` retains the actual source scheme
`U` and composes its atlas transformation with `e.hom`. The published
etale transport lemma and the surjective transport lemma above give the
geometric conditions; the structure morphism of `U` is unchanged, so its
local finite type property is retained.

`isAlgebraicSpace_of_presheafIso` applies the same diagonal and atlas
transport to two actual fppf sheaves. Both sheaves are inputs. The lemma
does not prove a new sheaf condition from etale descent, and does not
impose any quasi-separatedness or compactness condition.
