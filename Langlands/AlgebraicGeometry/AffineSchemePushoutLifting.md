# Reflecting affine spectrum pushouts

This internal helper reflects a pushout of actual underlying presheafed spaces
first to locally ringed spaces and then to schemes. The canonical spectrum
specializations retain the presheafed space pushout as an explicit premise.

## Reflection to locally ringed spaces

`isPushout_locallyRingedSpace_of_presheafedSpace` takes four arbitrary locally
ringed spaces in universe `u`, maps `f : W ⟶ X`, `g : W ⟶ Y`,
`i : X ⟶ Z`, and `j : Y ⟶ Z`, and a pushout square formed by their
underlying presheafed space morphisms. It proves `IsPushout f g i j` in the
full category of locally ringed spaces.

The proof first applies `IsPushout.of_map_of_faithful` to the fully faithful
functor `SheafedSpace.forgetToPresheafedSpace`. This recovers the pushout
square of the underlying sheafed spaces. Mathlib constructs colimits of
locally ringed spaces and proves that `LocallyRingedSpace.forgetToSheafedSpace`
preserves them. This forgetful functor also reflects isomorphisms.
The proof therefore installs
`reflectsColimit_of_reflectsIsomorphisms` for the span of `f` and `g`, and
applies `IsPushout.of_map_of_faithful` again. The faithfulness used in this
second step is supplied by Mathlib; fullness is not required.

`locallyRingedSpacePushoutIsColimit` constructs the `IsColimit` witness for
the actual locally ringed space cocone with point `Z` and legs `i`, `j`.
Its compatibility equation is the one recovered by the reflection theorem.
The witness is obtained from that theorem's colimit, and so provides descent
morphisms of locally ringed spaces with their factorization and uniqueness
laws for every compatible cocone.

## Reflection to schemes

`isPushout_scheme_of_locallyRingedSpace` takes four arbitrary schemes in
universe `u` and the analogous square of scheme morphisms. Its premise is
that their underlying locally ringed space morphisms form a pushout.
It reflects this square along the fully faithful functor
`Scheme.forgetToLocallyRingedSpace`.

The conclusion is a pushout in all schemes in universe `u`. In particular
its universal property allows arbitrary scheme targets.

## Canonical spectrum square

Let `B`, `C`, and `D` be arbitrary objects of `CommRingCat` in universe `u`,
with maps `f : B ⟶ D` and `g : C ⟶ D`. Write
`P = RingHom.pullback f.hom g.hom`, the compatible-pair subring of `B × C`.
Its projections are `f.hom.pullbackFst g.hom` and
`f.hom.pullbackSnd g.hom`, bundled as morphisms of `CommRingCat`.

Both canonical helpers assume that the actual images of `f`, `g`, and these
projections under `Spec.toPresheafedSpace` form a pushout square.
`isPushout_specLocallyRingedSpaceMap_of_presheafedSpace` concludes that the
square formed by `Spec.locallyRingedSpaceMap` is a pushout in locally ringed
spaces. `isPushout_specMap_of_presheafedSpace` then concludes that the
square formed by `Spec.map` is a pushout in schemes. The forgetful images
of these spectrum morphisms are definitionally the maps in the premises,
so the two specializations apply the general reflection helpers directly.

There is no surjectivity, nontriviality, reducedness, or separation
hypothesis in this conditional module. The presheafed space pushout
premise remains to be constructed for the assigned theorem; this module
does not prove `AffineSchemePushoutStatement`.

## Provenance

These are derived internal adapters for the affine scheme pushout proof.
They combine Mathlib's existing colimits of locally ringed spaces,
preservation by the sheafed space forgetful functor, reflection of
isomorphisms, and reflection of colimits by fully faithful functors.
They assert no additional external result. The implemented route uses
these categorical facts rather than constructing new descended stalk maps.
