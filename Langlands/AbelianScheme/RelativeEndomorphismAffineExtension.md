# Representability of relative homomorphisms from affine test schemes

Authors: Worker 1042.

This module proves that the relative Hom presheaf is represented on all
schemes over the base as soon as it is represented on the affine ones. Work
over an arbitrary base `S : Scheme.{u}` with actual
`G H : Langlands.GroupScheme.Cartier.CommGroupScheme S` and `E : Over S`.
All declarations live in namespace `Langlands.GroupScheme.Cartier`. The
module adds no axioms. It is a project-internal helper for the proof of
`Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityStatement`.
The underlying fact is standard: both the relative Hom presheaf and the
functor of points of `E` are Zariski sheaves, and a scheme is covered by
affine opens. The sheaf property of relative homomorphisms comes from
`Langlands.AbelianScheme.RelativeEndomorphismOfAffineHomSchemeGluing`.

## Notation

- `affineOverι S` is Mathlib's inclusion `ObjectProperty.ι` of the full
  subcategory of `Over S` on the objects `T` with `IsAffine T.left`.
- `affineCoverOver T i` and `affineCoverHom T i` are the member
  `T.left.affineCover.f i` of Mathlib's affine open cover, as an object over
  `S` and as a morphism to `T` over `S`. Instances record that its source is
  affine and that it is an open immersion.

## The extension theorem

Fix a natural isomorphism

`α : (affineOverι S).op ⋙ (relativeHomFunctor G H ⋙ forget AddCommGrpCat.{u}) ≅ (affineOverι S).op ⋙ yoneda.obj E`.

- `affHom α T` and `affInv α T` are the components of `α` and `α⁻¹` at an
  affine test object `T`. `affHom_restrict` and `affInv_comp` express their
  naturality for a morphism `b : T' ⟶ T` of affine test objects.
  `affHom_affInv` and `affInv_affHom` say that they are mutually inverse.
- `exists_universal_relativeHom α` gives `u : RelativeHom G H E` such that
  `restrict G H g u = affInv α T g` for every affine `T` and every
  `g : T ⟶ E`. Proof: the elements `affInv α _ (affineCoverHom E j)` on the
  affine open cover of `E.left` are compatible on all overlaps. This is
  checked on affine opens by `relativeHom_eq_of_forall_isAffine` and the
  naturality `affInv_comp`. They glue by `relativeHom_exists_glue` to some
  `u`. For an affine `T` and `g : T ⟶ E`, the identity is local on `T.left`
  (`relativeHom_eq_of_locally`). Around each point use an affine open `W` of
  the pullback of `g.left` and a member of the cover of `E.left`, so that
  `a ≫ g` factors through that member. Then combine `restrict_comp`, the
  gluing identity and `affInv_comp`.
- `nonempty_iso_yoneda_of_affine α`:
  `Nonempty ((relativeHomFunctor G H ⋙ forget AddCommGrpCat.{u}) ≅ yoneda.obj E)`,
  a natural isomorphism on all of `Over S`. Proof: for every `T : Over S`,
  the map `g ↦ restrict G H g u` from `T ⟶ E` to `RelativeHom G H T` is
  bijective.
  - Injectivity: compare on the affine open cover of `T.left`. There
    `restrict G H (affineCoverHom T i ≫ g) u` is
    `affInv α _ (affineCoverHom T i ≫ g)`, and `affHom α` recovers the
    morphism.
  - Surjectivity: given `χ`, the morphisms
    `affHom α _ (restrict G H (affineCoverHom T i) χ)` on the cover of
    `T.left` agree on overlaps. This is checked on affine opens of the
    overlaps with `affHom_restrict` and `restrict_comp`. They glue
    (`Scheme.Cover.glueMorphisms`) to some `g : T ⟶ E` over `S`. Then
    `restrict G H g u = χ` holds locally by `affInv_affHom`, hence globally
    by `relativeHom_eq_of_locally`.

  These bijections are natural in `T` by the published `restrict_comp`.
  `NatIso.ofComponents` assembles them into an isomorphism from
  `yoneda.obj E` to the relative Hom presheaf, and its inverse is the
  required isomorphism.
