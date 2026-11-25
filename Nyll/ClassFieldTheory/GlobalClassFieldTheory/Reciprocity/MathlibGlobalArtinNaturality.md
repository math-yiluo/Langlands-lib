# Naturality, finite projections and model independence of the global Artin map

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibGlobalArtinNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library's public global Artin map `mathlibGlobalArtin K`, on Mathlib's idèle class group of a number field `K`, is defined by transport from a small model `Shrink.{0} K` of `K`. This file shows that the transported isomorphism, on the quotient by the identity component, equals the reciprocity isomorphism built directly on `K`, that the public map is natural under `ℚ`-algebra isomorphisms of number fields, and that its projections to finite abelian extensions are the library's finite global Artin maps.

## Main definitions and results

- `mathlibIdeleClassCongr e`: for `e : K ≃ₐ[ℚ] M`, the induced isomorphism of Mathlib's idèle class groups as topological groups.
- `mathlibIdeleClassConnectedQuotientEquivAbelianization_value`: the native isomorphism (from the idèle class group modulo its identity component to the abelianised absolute Galois group), followed by `mathlibAbelianizationToMaximal`, sends the image of a class `a` to `maximalAbelianGlobalArtin` of the corresponding class in the library's idèle class group.
- `..._natural_mk` and `..._natural`: the native isomorphisms for `K` and `M` are intertwined by `e` and the induced map of abelianised absolute Galois groups.
- `mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse_eq_native`: the small-model transport equals the native isomorphism.
- `mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse_model`: for every `e : M ≃ₐ[ℚ] K`, the public isomorphism is the native one of `M` transported along `e`; `..._model_of_closure` allows any ring isomorphism of algebraic closures compatible with `e`.
- `mathlibGlobalArtin_toMaximal`: the image of `mathlibGlobalArtin K a` in `Gal(Kᵃᵇ / K)` is `maximalAbelianGlobalArtin`.
- `mathlibGlobalArtin_finiteProjection`: restricting to a finite Galois intermediate field `E` of the maximal abelian extension gives `globalIdeleClassArtinMonoidHom` for `E / K`; `..._of_scalarTower` gives the same for a finite abelian `L / K` with a `K`-compatible embedding into the maximal abelian extension.
- `mathlibGlobalArtin_baseEquiv`: `e` intertwines the public Artin maps of `K` and `M`.

Naturality comes from the semilinearity of the infinite global Artin map (`infiniteGlobalIdeleClassArtinMonoidHom_semilinear`) under the induced isomorphism of maximal abelian extensions. The equality with the native map is naturality applied to `Shrink K ≃ K`.

## Remarks

- Two idèle class groups are in play: Mathlib's `NumberField.IdeleClassGroup (𝓞 K) K` and the library's `IdeleClassGroup K`, compared by `ideleClassGroupContinuousMulEquivMathlib`.
- The normalisation is that of the library's maximal-abelian construction, called geometric in the comments.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/MathlibGlobalArtinNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `f4aabd9c6062ec741e2a5178ee77453d1efb5d3fe62ab9aaf167993c098f08b2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
