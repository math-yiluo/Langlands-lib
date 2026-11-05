# Actual normalizer images with a central torus complement

This internal construction supplies the forward normalizer comparison for
the derived-inclusion part of the source-apartment construction.

Work over any field `k : Type u`. Supply a homomorphism `q : D → G`, an
affine group `G`, acting commutative group schemes `T`, `S`, `A`, maps
`j : T → D`, `i : S → G`, `e : T → S`, `c : A → S`, and a square
`j ≫ q = groupHom e ≫ i`. Assume `i` is a maximal split torus, `T` and `A`
are split, `groupHom c ≫ i` is central on every test scheme, and the
actual product `centralComplementProduct e c : T × A → S` is flat and
surjective.

For a source normalizer point `n`, the source torus automorphism and the
commuting square describe conjugation on the retained factor. Centrality
makes conjugation trivial on the central factor. Thus after the product
parameterization, the conjugated ambient torus factors through the
original ambient torus.

The product is locally of finite presentation because both source and
target are split tori. Pull back this flat-surjective parameterization
along an arbitrary ambient torus point. The resulting cover is an
effective epimorphism, and membership in the represented ambient torus
descends through it. Hence the entire conjugated ambient torus has image
inside the original one on every test scheme. In particular they
commute. The published maximal-split-torus commutation theorem then
proves actual ambient normalizer membership.

`CentralComplementNormalizer.normalizerPointsMap` reuses the published
`DerivedNormalizerMap.normalizerPointsHom` with the reviewed affine
ambient-group interface. It is the original `rationalPoints.map q`
restricted to the actual normalizer groups; its coe lemma identifies
this forward map.
`normalizingAut_comp` proves that the source and image torus
automorphisms commute with the original map `e`. Its proof uses the
source and target conjugation equations and the monicity of `i`.

No central-isogeny, derived-subgroup, maximality of `j`, or surjectivity
of `e` alone is assumed. The intended application takes `q` to be the
actual derived inclusion. The tori, product and structural properties
remain supplied. No apartment or final normalizer-action equality is
asserted here.
