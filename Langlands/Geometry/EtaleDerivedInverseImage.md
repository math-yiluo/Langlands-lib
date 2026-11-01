# Exact geometric inverse image on derived categories

Author: Worker 13.

This internal construction applies the actual exact small-etale inverse image
to unbounded and bounded-below derived categories. Its homology comparison is
natural in every derived morphism. The bounded-below construction uses a proved
preservation of the original lower bound.

## Inputs and provenance

The input is an arbitrary morphism `f : Z ⟶ X` of schemes in universe `u` and a
commutative ring `R : Type u`. The categories `ModuleSheaf X R` and
`ModuleSheaf Z R` are sheaves of `ModuleCat.{u} R` on the actual small-etale
sites. No etale, affine, finite-type or Noetherian condition on `f` is imposed.
The two `HasDerivedCategory` instances have independent localization morphism
universes `wX` and `wZ`. They specify actual categorical localizations, rather
than supplied cohomology objects or comparison maps.

The underlying functor is `EtaleInverseImage.inverseImage f R`, constructed by
affine-site left Kan extension and sheafification. Its exactness on arbitrary
schemes is proved in `EtaleInverseImageExact`. Its additive and `R`-linear
structures are the existing structures on that same functor.

The construction uses pinned Mathlib
`Algebra/Homology/DerivedCategory/ExactFunctor.lean`,
`DerivedCategory/Plus.lean` and `DerivedCategory/TStructure.lean`, at commit
`5ed2965256430c3649e86755f9576b54eca72435`. It specializes the published
`Langlands.Cohomology.exactDerivedHomologyIso` from `ExactDerivedHomology`.
This is an internal derivation from these actual constructions, without a new
translation or claim about a Harris or Berkovich passage.

## Unbounded construction

`functor f R` is `(inverseImage f R).mapDerivedCategory`. Exactness ensures that
termwise inverse image preserves quasi-isomorphisms, so this is the actual
localized functor

```text
D(ModuleSheaf X R) → D(ModuleSheaf Z R).
```

The exported instances give its compatibility with integer shifts, its
triangulated structure and `R`-linearity. `factors` is the natural localization
comparison

```text
Q_X ⋙ functor f R
  ≅ (inverseImage f R).mapHomologicalComplex (up ℤ) ⋙ Q_Z.
```

`singleIso n` identifies the image of the actual singleton complex in any
integer degree `n` with the singleton of the ordinary inverse image.
`homologyIso q` is the natural isomorphism

```text
functor f R ⋙ Hq_Z ≅ Hq_X ⋙ inverseImage f R.
```

It is the existing exact-functor homology isomorphism descended through
localization, so it applies to all derived morphisms. The theorem
`homologyIso_naturality` states its naturality equation explicitly.

`preservesLowerBound` and `preservesUpperBound` prove that every original
cohomological bound is preserved. Their proofs use the homology
characterizations of the canonical t-structure: vanishing homology stays zero
under the additive inverse image, and `homologyIso` transports that zero object
to the homology of the derived image.

## Bounded-below construction

`plusFunctor f R` lifts the restriction of `functor f R` to
`DerivedCategory.Plus`, the full subcategory of objects with some lower
cohomological bound. For each input, its existing lower-bound witness is sent
to the same integer bound by `preservesLowerBound`. This proves membership in
the target full subcategory; no boundedness witness for the image is assumed.

`plusInclusionIso` identifies its composite with the inclusion into the
unbounded category with the original derived inverse image. The bounded-below
functor also has shift, triangulated and `R`-linear instances. Its linearity
proof applies the faithful inclusion and the unbounded functor's scalar
compatibility.

`plusHomologyIso q` is the restriction of `homologyIso q`.
`plusFactors` identifies this functor on localized bounded-below complexes
with localization of their termwise inverse images. `plusSingleIso n` gives
the corresponding singleton comparison for every integer degree. These last
two isomorphisms lift their unbounded counterparts through the fully faithful
inclusion; naturality follows by applying that faithful inclusion to the
unbounded naturality equations.

## Scope

Arbitrary geometric inverse image is not assumed to preserve injectives:
exactness and localization suffice for the present construction. This file
does not yet construct the adjunction to bounded-below derived direct image,
derived geometric composition or coefficient-change coherence, general
cohomological pullback, compact supports, smooth actions or the Harris tower
specialization.
