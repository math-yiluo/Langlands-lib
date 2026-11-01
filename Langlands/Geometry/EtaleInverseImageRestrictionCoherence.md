# Coherence of geometric inverse image and étale restriction

This module proves identity, composition and equality-transport coherence for
the existing canonical isomorphism `inverseImageIsoRestriction`. It also
constructs the comparison from successive geometric inverse images to
restriction along the composite and proves that this agrees with first
combining the geometric inverse images.

## Inputs and conventions

Schemes `X`, `Z`, `V` lie in universe `u`. For a scheme map `f : Z ⟶ X`,
geometric inverse image goes from sheaves on `X` to sheaves on `Z`.
All sheaves use the schemes' actual small étale sites. The restriction
construction requires `Etale f`: its underlying presheaf is precomposition
by the functor that composes an étale object over `Z` with `f`.

The five component formulas and the restriction identity/composition mate
calculations work for an arbitrary category `A : Type uA` with morphisms
in the independent universe `vA`. The comparisons with geometric inverse
image use any commutative ring `R : Type u`, and modules with carriers in
`u`, matching the scope of the existing geometric inverse image.
There are no derived-category, localization, field, finiteness or
local-constancy assumptions.

For the formulas below, write `L_f` for `inverseImage f R`,
`T_f` for `EtalePullback.restriction f (ModuleCat R)`, and
`c_f : L_f ≅ T_f` for `inverseImageIsoRestriction f R`.
The existing composition comparisons have directions
`L_f ⋙ L_g ≅ L_(g ≫ f)` and `T_f ⋙ T_g ≅ T_(g ≫ f)`.
Equality transport always keeps the displayed equality of base maps.

## Component and mate calculations

The component lemmas expose the actual presheaf maps used by the existing
constructions:

- `restriction_map_hom_app` evaluates a restricted sheaf morphism on
  the object obtained by composing its structure map with `f`.
- `restrictionId_hom_app_hom_app` expresses the restriction identity
  comparison as the presheaf applied contravariantly to the inverse
  of the site composition identity comparison.
- `restrictionComp_hom_app_hom_app` expresses restriction composition as
  the presheaf applied contravariantly to the site composition comparison.
- `restrictionGeometricAdjunction_counit_app_hom_app` identifies the
  sheaf adjunction counit with the presheaf applied contravariantly to
  the unit of the composition/base-change adjunction on étale objects.
- `directImageComp_inv_app_hom_app` identifies the inverse direct-image
  comparison with the presheaf applied contravariantly to the inverse
  fiber-product composition comparison.

`conjugate_restrictionId` and `conjugate_restrictionComp` prove that the
mates of the restriction identity and composition maps are precisely the
inverses of `directImageId` and `directImageComp`. These statements use
the geometric right adjoint supplied by `restrictionGeometricAdjunction`,
rather than the earlier right-Kan presentation of direct image.

The implemented proofs apply the injective inverse adjunction hom-equivalence,
use the counit characterization of mates, and then evaluate at an actual
étale object. Presheaf functoriality reduces the equalities to maps of
étale objects. The identity calculation uses the explicit site adjunction;
the composition calculation proves equality of the underlying scheme maps
by both fiber-product projections.

## Canonical comparison laws

`conjugate_inverseImageIsoRestriction` proves that the mate of `c_f.hom`
is the identity on geometric direct image. Its proof is the counit
compatibility of the existing `Adjunction.leftAdjointUniq` construction.
In particular, it computes the already constructed comparison.

`inverseImageIsoRestriction_id` proves

```text
c_id.hom ≫ restrictionId.hom = inverseImageId.hom.
```

`inverseImageIsoRestriction_comp` proves

```text
inverseImageComp(f,g).hom ≫ c_(g≫f).hom =
  whiskerRight(c_f.hom, L_g) ≫
  whiskerLeft(T_f, c_g.hom) ≫ restrictionComp(f,g).hom.
```

Both equations follow by injectivity of the mate equivalence, its
composition and whiskering laws, and the computed restriction and
geometric mates. For composition, the remaining whiskered identity maps
are checked componentwise.

`compositeInverseImageIsoRestriction` constructs the isomorphism on the
right of the composition equation: first compare `L_f` to `T_f`, then
`L_g` to `T_g`, then compose restrictions.
`compositeInverseImageIsoRestriction_eq` upgrades that equation to
equality of natural isomorphisms with
`inverseImageComp R f g ≪≫ inverseImageIsoRestriction (g ≫ f) R`.

For `e : f = k`, with both maps étale,
`conjugate_restrictionCongr` identifies the mate of restriction equality
transport with the inverse geometric direct-image equality comparison.
After substitution, the proof checks that the reflexive fiber-product
comparison is the identity by its two projections.
`inverseImageIsoRestriction_congr` then proves

```text
inverseImageCongr(e).hom ≫ c_k.hom =
  c_f.hom ≫ restrictionCongr(e).hom.
```

Its proof again uses injectivity and composition of mates. Thus the
comparison retains the equality transports needed for diagrams whose
scheme functor laws hold propositionally.

## Provenance and remaining scope

This is an internal construction and coherence group for the project's
existing geometric and restriction functors, using Mathlib adjunction
mates and actual fiber products. It introduces no external mathematical
assertion or assumed compatibility. The imported constructions are
`EtaleInverseImageRestriction`, `EtaleInverseImageCoherence`,
`EtaleImageFunctoriality`, and the restriction equality transport from
`EtaleCohomologyDiagram`.

The category equivalence between geometric and restriction coefficient
diagrams and its cohomological comparisons remain subsequent constructions.
This module does not provide compact supports, smooth equivariance,
coefficient-ring changes, tower limits or the Harris specialization.
