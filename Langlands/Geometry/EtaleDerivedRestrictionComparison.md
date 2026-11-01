# Geometric derived pullback and étale restriction

This module proves that the actual geometric pullback from the constructed
derived adjunction agrees, along an étale scheme map, with the earlier
pullback defined by restriction on the small étale sites.

The schemes `X`, `Z`, the commutative coefficient ring `R`, and the module
carriers lie in universe `u`. The map `f : Z ⟶ X` is étale.
The sheaf categories on `X` and `Z` and the coefficient module category have
independently chosen derived localization universes `wX`, `wZ`, and `wR`.
No field, Noetherian, finiteness, or local-constancy assumption is imposed.

The existing `inverseImageIsoRestriction f R` identifies actual geometric
inverse image with the restriction functor obtained by composing étale
structure morphisms with `f`. Write its component as
`e_F : inverseImage(f)(F) ≅ restriction(f)(F)`. This is the constructed
adjunction comparison, not a supplied cohomological comparison.

`sheafDerivedPullback_restriction_eq` proves equality of the actual natural
transformations after composing geometric pullback with derived sections
of `e_F.hom`. Its component equation, also provided as
`sheafDerivedPullback_restriction`, is

```text
sheafDerivedPullback(f)_F ≫ derivedSections(Z).map(e_F.hom)
  = EtalePullback.derivedSectionsMap(f)_F.
```

The proof first uses the actual resolution comparison
`sheafDerivedPullback_eq_derivedMap`. It then applies
`DerivedPlusSource.derivedMap_whiskerRight` to the natural transformation
given by the constructed inverse-image/restriction iso. The proved
ordinary section equality `sectionsPullback_restriction_eq` identifies the
transported square with the one defining `derivedSectionsMap`.
The comparison of derived maps is therefore proved from actual
augmentation and section compatibilities; none of these equalities is a
construction input.

`sheafDerivedPullbackRestrictionIso F` packages this equation as an actual
isomorphism in the arrow category of the bounded-below derived coefficient
category. Its source endpoint is the identity on derived sections over
`X`; its target endpoint is derived sections over `Z` applied to `e_F`.
The preceding equation proves its commuting-square field.

For every `q : ℕ`, `cohomologyPullback_restriction` proves

```text
cohomologyPullback(f,q)_F ≫ cohomology(Z,q).map(e_F.hom)
  = EtalePullback.cohomologyMap(f,q)_F.
```

The natural-transformation version is
`cohomologyPullback_restriction_eq q`. The proof expands the definition of
geometric ordinary cohomology pullback through the canonical
`homologyNatIso` identifications. Naturality of the target identification
moves `e_F.hom` to the derived coefficient map. The proved derived-map
equation and the earlier `derivedSectionsMap_homology` then give the
result, after cancellation of the source identification.
`cohomologyPullbackRestrictionIso q F` constructs the associated actual
arrow isomorphism, with identity source and `cohomology(Z,q).mapIso e_F`
as its target endpoint.

The provenance is internal: the module compares existing geometric and
resolution constructions and proves their compatibility using the imported
actual maps. It does not assert compact support, scalar-change coherence,
smooth equivariance, or the geometric Harris specialization. Those remain
separate construction or theorem obligations.
