# Inverse image of constant sheaves along arbitrary morphisms of schemes

This internal construction identifies the existing constructed inverse image
of a constant étale sheaf with the constant sheaf on the new base, for an
arbitrary morphism of schemes. The comparison is natural in the coefficient
module and is characterized by global sections. It respects identities and
composites, agrees with the existing étale-restriction comparison when the
morphism is étale, and preserves coefficient group actions. All declarations
are in namespace `Langlands.Geometry.EtaleInverseImage`.

## Parameters and scope

Let `X Z : Scheme.{u}`, let `f : Z ⟶ X` be any morphism, and let
`R : Type u` be a commutative ring. Sheaves take values in `ModuleCat.{u} R`
on the small étale sites. There is no étale, finiteness, finite-type,
Noetherian or field hypothesis on `f`, and no hypothesis on the coefficient
module. Only the étale compatibility section assumes `[Etale f]`.

The inputs are the existing `inverseImage f R` and its adjunction
`inverseImageAdjunction f R` with the existing direct image `directImage f`;
the existing global-section functor `sections X R`, which is Mathlib's
`Sheaf.Γ`; and the existing natural isomorphism
`directImageSectionsIso f R : directImage f ⋙ sections X R ≅ sections Z R`.
`constantSheafΓAdj` is Mathlib's adjunction between the constant-sheaf
functor and `Sheaf.Γ`. The existing `sectionsPullback f R` is the
global-section map `sections X R ⟶ inverseImage f R ⋙ sections Z R`.

## The comparison

- `constantDirectImageSectionsAdj f R` is the adjunction between the constant
  sheaf functor on `Z` and `directImage f ⋙ sections X R`. It transports
  `constantSheafΓAdj` on `Z` along the inverse of `directImageSectionsIso`.
  `constantDirectImageSectionsAdj_unit_app` states that its unit at `M` is
  the constant-sheaf unit on `Z` followed by that inverse comparison.
- `inverseImageConstantIso f R` is the natural isomorphism

  ```text
  constantSheaf X ⋙ inverseImage f R ≅ constantSheaf Z.
  ```

  The composite of `constantSheafΓAdj` on `X` with `inverseImageAdjunction`
  makes the source left adjoint to `directImage f ⋙ sections X R`, and so does
  `constantDirectImageSectionsAdj`. The isomorphism is Mathlib's
  `Adjunction.leftAdjointUniq` for these two adjunctions. No comparison of
  constant sheaves is supplied as input.

## Characterization by global sections

- `sectionsPullback_app_eq` unfolds the existing global-section pullback: at a
  sheaf `F` it is sections of the inverse-image adjunction unit at `F`,
  followed by `directImageSectionsIso` at the inverse image of `F`.
- `inverseImageConstant_hom_ext` states that two maps `φ ψ` from the inverse
  image of the constant sheaf on `M` to a sheaf `H` on `Z` are equal when they
  agree after the composite of the constant-sheaf unit at `M` on `X`, the
  global-section pullback, and sections on `Z`. The proof identifies this
  composite, after `directImageSectionsIso` at `H`, with the adjunction
  bijection of the composite adjunction; that bijection is injective.
- `unit_sectionsPullback_inverseImageConstantIso` states that the constant-sheaf
  unit at `M` on `X`, followed by global-section pullback and sections of the
  comparison, is the constant-sheaf unit at `M` on `Z`. It follows from
  Mathlib's `Adjunction.unit_leftAdjointUniq_hom_app`, the unit formula above,
  and naturality of `directImageSectionsIso`. By the previous lemma, this
  equation determines the comparison.

## Identity and composition

These follow from the characterization and the existing identity and
composition laws `sectionsPullback_id` and `sectionsPullback_comp` of
global-section pullback.

- `inverseImageConstantIso_id` states that, along `𝟙 X`, the comparison at `M`
  is the existing identity comparison `inverseImageId R X` at the constant
  sheaf on `M`.
- `inverseImageConstantIso_comp g` states, for `g : V ⟶ Z`, that the existing
  composition comparison `inverseImageComp R f g` at the constant sheaf,
  followed by the comparison for `g ≫ f`, equals inverse image along `g` of the
  comparison for `f`, followed by the comparison for `g`. The proof also uses
  naturality of global-section pullback along `g`.

## Étale morphisms

For `[Etale f]` the Library already has `EtalePullback.constantPullbackIso`,
comparing étale restriction of constant sheaves with constant sheaves, and
`inverseImageIsoRestriction f R`, identifying inverse image with étale
restriction. Its section map `EtalePullback.sectionsMap f R` restricts
sections over the terminal object.

- `constantSheafΓAdj_unit_sectionsIso W M` states that, on any scheme `W`, the
  constant-sheaf unit followed by the existing `sectionsIso W R` (evaluation
  at the terminal object) is the sheafification unit of the constant presheaf,
  evaluated at the terminal object. It uses Mathlib's
  `Adjunction.unit_rightAdjointUniq_hom_app`.
- `unit_sectionsMap_constantPullbackIso` states the étale analogue of the
  normalization: the constant-sheaf unit on `X`, followed by
  `EtalePullback.sectionsMap` and sections of `constantPullbackIso`, is the
  constant-sheaf unit on `Z`. The proof evaluates at terminal objects, uses
  naturality of the sheafification unit, and uses the existing
  `constantPullbackIso_hom_unit`.
- `inverseImageConstantIso_etale` states that
  `inverseImageIsoRestriction f R` at the constant sheaf on `M`, followed by
  `constantPullbackIso` at `M`, is the new comparison at `M`. The proof uses
  `inverseImageConstant_hom_ext`, the existing `sectionsPullback_restriction`,
  and the previous lemma.

## Coefficient group actions

For a monoid `G : Type u`, `inverseImageConstantActionIso f R G` is the natural
isomorphism

```text
(constantSheaf X).mapAction G ⋙ (inverseImage f R).mapAction G
  ≅ (constantSheaf Z).mapAction G.
```

It composes Mathlib's `Functor.mapActionComp` with
`Functor.mapActionCongr` applied to the comparison. It therefore intertwines
every group operator and is natural in equivariant module maps.
`inverseImageConstantActionIso_hom_hom` and `_inv_hom` identify its
underlying sheaf maps with the comparison and its inverse at the underlying
module.

## Provenance and scope

This is internal categorical infrastructure: uniqueness of left adjoints in
Mathlib applied to the existing constructed inverse-image adjunction, the
existing section comparison for direct images, and Mathlib's constant-sheaf
adjunctions. No external-literature statement is formalized. The module does
not treat associated sheaves of torsors, locally constant sheaves, derived
inverse images or cohomology. The comparison of inverse image with
association on base-changed covers, for an arbitrary morphism, remains a
separate obligation of the broader Harris task.
