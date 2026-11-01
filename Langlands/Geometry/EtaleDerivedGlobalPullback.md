# Derived global sections and arbitrary geometric pullback

Author: Worker 13.

This internal construction identifies derived global sections of actual
derived direct image with derived global sections on the source scheme.
Composing this comparison with the constructed derived adjunction unit gives
pullback of derived global sections. On sheaves in degree zero, homology then
gives natural maps on the existing small-etale cohomology functors.

## Inputs and provenance

The input is any scheme morphism `f : Z ⟶ X` and commutative coefficient ring
`R : Type u`, with both schemes in universe `u`. Sheaves have values in
`ModuleCat.{u} R` on the actual small-etale sites. Three independent
`HasDerivedCategory` instances specify localization morphism universes `wX`,
`wZ` and `wR` for the two sheaf categories and the coefficient-module category.
No etale, affine, flatness, finite-type or Noetherian hypothesis on `f` occurs.

The file uses the actual inverse/direct-image functors and derived
adjunction from `EtaleDerivedAdjunction`, the terminal/global-section
comparison and injective preservation from `EtaleDerivedDirectImage`, and the
actual global-section derived functors and natural homology comparisons from
`EtaleDerivedSectionsPlus`. The latter isomorphisms identify homology with the
published `EtaleDerivedSections.cohomology` functors.

The categorical steps use pinned Mathlib
`Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean`,
`CategoryTheory/Localization/DerivabilityStructure/Derives.lean`,
`CategoryTheory/Functor/Derived/RightDerived.lean`, and the termwise complex
functors and full subcategory inclusions, at commit
`5ed2965256430c3649e86755f9576b54eca72435`. This is an internal derivation from
these constructions; it does not claim a new source translation or Harris
specialization.

## Injective complexes and actual section complexes

`directImageInjectives` restricts actual geometric direct image to the full
subcategories of injective sheaves. Its membership proof uses the established
injective preservation of direct image, which follows from exactness of its
constructed inverse-image left adjoint.

`sectionUnit_directImage_injectiveComplex` proves that the right-derived
global-section unit is invertible on the direct image of every bounded-below
complex of injectives. The image is itself represented by a bounded-below
complex in the target's full injective subcategory, so Mathlib's invertibility
instance applies. The construction retains its additive structure.

`sectionsComplexIso` applies the actual comparison `Γ_X f_* ≅ Γ_Z` termwise.
It is a natural isomorphism from direct image of bounded-below complexes
followed by termwise global sections on `X` to termwise global sections on `Z`.
It lifts the existing `mapHomologicalComplexCompIso` through the fully
faithful bounded-below inclusion. Its naturality proof uses the naturality of
that actual unbounded complex comparison.

## Deriving the composite

Write `D` for ordinary geometric direct image, `RD` for its actual right
derived functor, and `RΓ_X` and `RΓ_Z` for the existing derived section
functors. The natural transformation `compositeUnit` has type

```text
Γ_Z.mapCochainComplexPlus ⋙ Q_R ⟶ Q_Z ⋙ (RD ⋙ RΓ_X).
```

On a bounded-below complex `K` it first uses the inverse of
`sectionsComplexIso` to identify its original section complex with
`Γ_X(D K)`. It then uses the global-section right-derived unit on `D K`,
followed by `RΓ_X` applied to the direct-image right-derived unit on `K`.
Functor associators make the displayed domain and target exact.

`composite_isRightDerivedFunctor` proves that this is a right-derived
comparison. The injective-complex derivability structure computes the
right-derived global-section functor. On each of its injective complex
objects, all three maps just described are invertible: the first is an
isomorphism, the second uses injective preservation by `D`, and the third is
the image of an invertible direct-image derived unit. The derivability
criterion proves the universal property.

Uniqueness of right-derived functors therefore constructs
`directImageSectionsIso`:

```text
RD ⋙ RΓ_X ≅ RΓ_Z.
```

`directImageSectionsIso_unit` proves its normalization against
`compositeUnit` and the original global-section derived unit, on every
complex representative. This is a comparison of actual derived functors,
rather than an assertion that global sections commute with the individual
higher-direct-image sheaves.

## Pullback maps

For an arbitrary bounded-below derived sheaf `K` over `X`, `derivedPullback`
is the component of a natural transformation

```text
RΓ_X ⟶ derivedInverseImage ⋙ RΓ_Z.
```

`derivedPullback_app` states its formula: apply `RΓ_X` to the constructed
derived adjunction unit `K → RD(derivedInverseImage K)`, then apply
`directImageSectionsIso` at `derivedInverseImage K`.

`sheafDerivedPullback` restricts to actual sheaves placed in degree zero and
then uses `EtaleDerivedInverseImage.plusSingleIso` to identify derived
inverse image of the singleton with the singleton of ordinary inverse image.
Its target is precisely ordinary inverse image followed by the existing
derived-section functor for sheaves.

For every `q : ℕ`, `cohomologyPullback q` is the natural transformation

```text
cohomology X R q ⟶ inverseImage f R ⋙ cohomology Z R q.
```

It conjugates homology of `sheafDerivedPullback` by the published natural
homology comparisons on both schemes. `cohomologyPullback_naturality` states
the resulting coefficient-morphism equation explicitly. The maps act on the
existing cohomology objects; no new cohomology groups or desired pullback maps
are supplied as input.

## Scope

Ordinary direct image is not claimed exact, and arbitrary inverse image is
not assumed to preserve injectives. Geometric identity and composition laws
for these new maps, their degree-zero identification with ordinary section
pullback, agreement with the older etale-restriction model, coefficient-ring
coherence, compact supports, smooth actions and the Harris tower
specialization remain separate obligations.
