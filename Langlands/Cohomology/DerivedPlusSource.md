# Derived complexes along exact injective-preserving source functors

Author: Worker 13.

This module constructs a natural transformation of actual bounded below
derived objects from a square of additive functors. Let `C`, `D` and `E`
be abelian categories, with independent object and morphism universes
`uC`, `vC`, `uD`, `vD`, `uE`, `vE`. Choose their derived categories in
independent localization universes `wC`, `wD`, `wE`, and assume `C` and `D`
have enough injectives. Let

\[
F:C\longrightarrow E,\quad T:C\longrightarrow D,\quad G:D\longrightarrow E
\]

be additive, with `T` preserving homology and injective objects. The input
is an actual natural transformation `τ : F ⟶ T ⋙ G`. The constructed map is

\[
\operatorname{derivedComplex}(F)\longrightarrow
T\mathbin{\ggg}\operatorname{derivedComplex}(G).
\]

Here `derivedComplex` is the published construction: place an object in
degree zero and apply Mathlib's right derived functor on bounded below
derived categories. Neither `F` nor `G` is assumed exact or left exact.
Exactness and injective preservation are required of `T`.

## Resolution representatives

For an injective resolution `I` of `X`, `imageResolution F I` applies `F`
to the natural-indexed complex and extends the result by zero along
`ComplexShape.embeddingUpNat`. It is an actual integer-indexed cochain
complex strictly concentrated in degrees at least zero. The bounded below
property is proved by Mathlib's extension instance.

`imageResolutionComparison` compares applying `F` before extension with
applying it after extension. It uses the published `mapExtendIso`, lifted
through the fully faithful inclusion of bounded below complexes.
`imageResolutionIso` then identifies the localization of this complex
with the existing `derivedComplex F` using `derivedComplexIso`.

`imageResolutionMap` extends `F` applied to a compatible resolution lift.
`imageResolutionIso_hom_naturality` proves that its localization recovers
the map of `derivedComplex F`. The proof combines
`derivedComplexIso_hom_naturality` with the extension comparison's
naturality.

## The square and resolution independence

`mapResolutionHom T φ` applies `T` to a compatible resolution map `φ`.
Its source and target are the actual mapped injective resolutions from
`DerivedComparison.mapInjectiveResolution`. Its augmentation compatibility
is proved by `mapInjectiveResolution_comm`; no lift compatibility is
assumed.

`resolutionSquare F T G τ I` applies `τ` degreewise to `I.cocomplex`.
The target is `G` applied to the mapped resolution `T(I)`.
`imageResolutionSquare` extends this map to integer degrees.
`imageResolutionSquare_naturality` follows from naturality of `τ` on
complexes and preservation of composition by extension.

`derivedMapOfResolution` conjugates the localization of this square by
the two `imageResolutionIso` identifications. Thus it is a morphism
from the existing derived object of `F` at `X` to the existing derived
object of `G` at `T X`. `derivedMapOfResolution_naturality` proves
naturality along every compatible resolution lift: it cancels the
target comparison isomorphism, applies the representative naturality
identities, and localizes the square.

Applying this naturality to a lift of `𝟙 X` proves
`derivedMapOfResolution_eq`: any two injective resolutions give the
same morphism. `derivedMap` uses Mathlib's chosen resolutions to define
the natural transformation; `derivedMap_app` proves that every resolution
computes its components. Strict functoriality of arbitrarily chosen raw
resolution maps is unnecessary.

## Recovery of ordinary cohomology

`localizedHomologyIso K n` compares degree `n : ℤ` cohomology of the
localization of `K` with `K.obj.homology n`. Its naturality follows from
the comparison of the bounded below and unbounded localization functors
and `DerivedCategory.homologyFunctorFactors`.

For `q : ℕ`, `imageHomologyIso F I q` further uses
`extendHomologyIso` to recover homology of the natural-indexed image
complex. `imageHomologyIso_comp` proves that composing this with the
image-resolution identification and the inverse of
`I.isoRightDerivedObj F q` gives exactly the already published
`DerivedPlus.homologyIso F I q`.

`imageHomologyIso_square` identifies the map of localized cohomology of
the extended square with homology of `resolutionSquare`. This is the
naturality of the localization comparison followed by naturality of
`extendHomologyIso`.

Finally, `derivedMap_homology` states the resulting formula. Under the
published `homologyIso` identifications, the cohomology map is

\[
(F.\mathrm{rightDerived}\ q)(X)
\xrightarrow{\ (I.\mathrm{isoRightDerivedObj}\ F\ q).\mathrm{hom}\ }
H^q(F(I))
\xrightarrow{\ H^q(\tau_I)\ }
H^q(G(T(I)))
\xrightarrow{\ (T(I).\mathrm{isoRightDerivedObj}\ G\ q).\mathrm{inv}\ }
(G.\mathrm{rightDerived}\ q)(T X).
\]

The Lean equality includes the initial identification from cohomology
of `derivedComplex F` to `F.rightDerived q`. Its proof substitutes
`imageHomologyIso_comp`, cancels the intervening isomorphisms and uses
`imageHomologyIso_square`.

## Provenance and scope

This is internal homological algebra derived from the published
[`DerivedPlusNaturality`](DerivedPlusNaturality.md),
[`DerivedComparison`](DerivedComparison.md), and
[`ExtendMap`](ExtendMap.md) modules. It uses the pinned Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`, particularly
`Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean`,
`Algebra/Homology/Embedding/ExtendHomology.lean`, and
`CategoryTheory/Abelian/RightDerived.lean`. The proof descriptions above
describe the implemented Lean arguments. No new original-literature
claim or assumed derived compatibility is introduced.

The transformation is on objects of `C`, regarded as complexes in degree
zero. This module does not construct a transformation whose source is
the whole derived category of `C`. Compatibility under identities and
compositions of source functors, actions, compact supports and inverse
limits is outside this unit.
