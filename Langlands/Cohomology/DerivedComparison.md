# Comparing right derived functors along exact functors

Author: Worker 13.

This module proves a general comparison of right derived functors in abelian
categories. It uses Mathlib's right derived functors `Functor.rightDerived`,
which are computed from chosen injective resolutions. Here `C`, `D`, `E` and
`E'` are abelian categories, and `C` and `D` have injective resolutions.

## Mapping resolutions

Let `T : C ⥤ D` be additive and preserve homology, which in abelian categories
means that it is exact. Suppose also that it preserves injective objects
(`Functor.PreservesInjectiveObjects`). `mapInjectiveResolution T I` applies
`T` termwise to an injective resolution `I` of `X`. Its augmentation is the
image of the augmentation of `I`, identified with a map out of the single
complex on `T X`. Its terms are injective because `T` preserves injective
objects. The augmentation is a quasi-isomorphism because exact functors
preserve quasi-isomorphisms (Mathlib's
`HomologicalComplex.quasiIso_map_of_preservesHomology`). The theorem
`mapInjectiveResolution_ι_f_zero` gives the degree-zero augmentation. The
theorem `mapInjectiveResolution_comm` shows that the image of a chain map
lifting `f : X ⟶ Y` lifts `T.map f`.

## Exact functors and homology

For an exact functor `P : E ⥤ E'`, `mapHomologyIso P K q` is Mathlib's
comparison `ShortComplex.mapHomologyIso`. It identifies the degree-`q`
homology of the termwise image of a cochain complex `K` with the image of the
homology of `K`. `mapHomologyIso_inv_naturality` records its naturality in
`K`.

## The comparison

Let `Φ : C ⥤ E` and `Ψ : D ⥤ E'` be additive, and let
`e : Φ ⋙ P ≅ T ⋙ Ψ`. `complexIso` applies `e` termwise to a cochain complex.
It is natural (`complexIso_hom_naturality`).

For an injective resolution `I` of `X`, `compIsoOfResolution` composes four
isomorphisms:

1. `P` applied to Mathlib's isomorphism between `(Φ.rightDerived q).obj X`
   and the homology of `Φ` applied to `I`;
2. the inverse of `mapHomologyIso`;
3. the homology of `complexIso` at `I`;
4. the inverse of Mathlib's isomorphism between
   `(Ψ.rightDerived q).obj (T.obj X)` and the homology of `Ψ` applied to the
   mapped resolution `mapInjectiveResolution T I`.

`compIsoOfResolution_naturality` proves compatibility with a morphism
`f : X ⟶ Y` and any chain map between resolutions lifting it. It combines
Mathlib's naturality lemmas for `InjectiveResolution.isoRightDerivedObj`, the
lifting property of `mapInjectiveResolution`, and the naturality of the
intermediate isomorphisms.

`rightDerivedCompIso Φ P T Ψ e q` is the resulting natural isomorphism
`Φ.rightDerived q ⋙ P ≅ T ⋙ Ψ.rightDerived q`. It is built from Mathlib's
chosen resolutions `injectiveResolution X`, with naturality witnessed by the
lifts `InjectiveResolution.desc`.

## Provenance and scope

This is standard homological algebra, stated and proved here as internal
infrastructure. It is the general form of the argument that an exact functor
preserving injectives, such as forgetting equivariance on sheaves, lets
derived functors be computed after applying it. Berkovich, *Etale equivariant
sheaves on p-adic analytic spaces* (unfinished 1995–1996 manuscript), section
1.5, Corollary 1.5.2(i), printed pp.11–12, compares derived functors of
compactly supported sections of `G`-sheaves with compactly supported
cohomology of the underlying sheaves. Worker 13 read this passage in the
original. Berkovich's proof uses soft resolutions instead. This module
contains no sheaf-theoretic statement. The specialization to equivariant
sheaves is a separate obligation.

Source registration:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The module imports only Mathlib.
