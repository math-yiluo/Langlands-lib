# Iterated affine spaces and their function fields

Author: Worker 1630.

This derived helper module depends only on Mathlib. It compares affine
space on a disjoint sum of coordinates with iterated affine space, and
compares their function fields. All schemes and coordinate types live in
one arbitrary universe `u`. Coordinate types are arbitrary; no finiteness
is assumed.

## Generic points

Three topological facts are stated for arbitrary topological spaces.

- `isGenericPoint_univ_of_denseRange`: a continuous map with dense range
  sends a generic point of its source to a generic point of its target.
  The image of a generic point is a generic point of the closure of the
  image, and that closure is the whole target.
- The reused `SchemeFiberGeometry.isGenericPoint_of_isInducing`: if `f` is inducing and `f x` is a
  generic point of the target, then `x` is a generic point of the source.
  An inducing map reflects specialization.
- `denseRange_of_isGenericPoint`: a map whose range contains a generic
  point of the target has dense range.

## Affine space on a sum of coordinates

For coordinate types `m`, `n` and a scheme `S`, `affineSpaceSumIso m n S`
is an isomorphism `𝔸(m ⊕ n; S) ≅ 𝔸(n; 𝔸(m; S))`. The coordinates indexed
by `m` become the coordinates of the inner affine space `𝔸(m; S)`, and the
coordinates indexed by `n` become those of the outer affine space.

- The forward map is built with Mathlib's `AffineSpace.homOfVector` twice.
  The inner map `𝔸(m ⊕ n; S) ⟶ 𝔸(m; S)` lies over the structure map to `S`
  and has coordinates `coord (Sum.inl i)`. The outer map has coordinates
  `coord (Sum.inr j)`.
- The inverse lies over the composite `𝔸(n; 𝔸(m; S)) ⟶ 𝔸(m; S) ⟶ S`. Its
  coordinates are `Sum.elim` of the pulled-back inner coordinates and the
  outer coordinates.
- Both composites are identities by `AffineSpace.hom_ext`: they agree over
  the base and on every coordinate.

`affineSpaceSumIso_hom_over` and `affineSpaceSumIso_inv_over` state that
the two maps commute with the structure maps to `S`. On the iterated side
the structure map is the composite `𝔸(n; 𝔸(m; S)) ⟶ 𝔸(m; S) ⟶ S`.

## Maps of function fields

Let `X` and `Y` be irreducible schemes and `f : X ⟶ Y` a morphism sending
the generic point of `X` to the generic point of `Y`; the hypothesis `hf`
records this equation. `functionFieldMap f hf : Y.functionField ⟶
X.functionField` is the stalk map of `f` at the generic point of `X`,
preceded by the identification of stalks given by `hf` (Mathlib's
`stalkSpecializes`).

- `SpecMap_functionFieldMap_fromSpecStalk`: the square formed by
  `Spec.map (functionFieldMap f hf)`, the two canonical morphisms
  `fromSpecStalk` at the generic points, and `f` commutes. This follows
  from the Mathlib identities for `stalkSpecializes` and `stalkMap`.
- `isIso_functionFieldMap`: if `X` and `Y` are integral and `f` is a
  preimmersion, then `functionFieldMap f hf` is an isomorphism. The map is
  injective as a ring map between fields. It is surjective because a
  preimmersion is surjective on stalks and the stalk identification is an
  isomorphism.

## The iterated function field

Now let `S` be an integral scheme and let `K` be the function field of
`𝔸(m; S)`.

- `affineSpaceFunctionFieldToSum m n S : 𝔸(n; Spec K) ⟶ 𝔸(m ⊕ n; S)` is
  `AffineSpace.map n` of the generic-point morphism `Spec K ⟶ 𝔸(m; S)`,
  followed by the inverse of `affineSpaceSumIso`.
- `affineSpaceFunctionFieldToSum_over` states that it lies over `S`, where
  `𝔸(n; Spec K)` maps to `S` through `Spec K ⟶ 𝔸(m; S) ⟶ S`.
- Two instances record that `AffineSpace.map n` of the generic-point
  morphism, and hence `affineSpaceFunctionFieldToSum m n S`, are
  preimmersions. The generic-point morphism `fromSpecStalk` is a
  preimmersion in Mathlib. Preimmersions are stable under base change, and
  Mathlib's `AffineSpace.isPullback_map` exhibits `AffineSpace.map n` as a
  base change. Isomorphisms are preimmersions, and preimmersions are
  closed under composition.
- `affineSpaceFunctionFieldToSum_genericPoint` states that this morphism
  sends the generic point to the generic point. The structure map
  `𝔸(n; 𝔸(m; S)) ⟶ 𝔸(m; S)` is surjective, so it sends the generic point
  to the generic point. The point of `Spec K` also maps to the generic
  point of `𝔸(m; S)`. By the pullback square `AffineSpace.isPullback_map`
  and Mathlib's `Scheme.exists_preimage_of_isPullback`, the generic point
  of `𝔸(n; 𝔸(m; S))` has a preimage `p` in `𝔸(n; Spec K)`. The base-changed
  map is an embedding, so `p` is a generic point, hence the generic point.
  Finally the inverse of `affineSpaceSumIso` is surjective and preserves
  the generic point.
- `functionFieldAffineSpaceSumIso m n S` is the resulting isomorphism from
  the function field of `𝔸(m ⊕ n; S)` to the function field of
  `𝔸(n; Spec K)`. It is `functionFieldMap` of
  `affineSpaceFunctionFieldToSum m n S`, which is an isomorphism by
  `isIso_functionFieldMap`.
- `SpecMap_functionFieldAffineSpaceSumIso_hom_fromSpecStalk` is the
  corresponding commuting square of `fromSpecStalk` morphisms.
- `iteratedFunctionFieldOverIso m n S` is an isomorphism in `Over S`. Its
  source is the spectrum of the function field of `𝔸(n; Spec K)`, over `S`
  through `𝔸(n; Spec K) ⟶ Spec K ⟶ 𝔸(m; S) ⟶ S`. Its target is the
  spectrum of the function field of `𝔸(m ⊕ n; S)`, over `S` through its
  generic point. The underlying isomorphism is `Spec.map` of
  `functionFieldAffineSpaceSumIso`. Compatibility with the structure maps
  is the previous commuting square together with
  `affineSpaceFunctionFieldToSum_over`.

For `S = Spec k` with `k` a field, the function field of `𝔸(m ⊕ n;
Spec k)` is the rational function field in the coordinates `m ⊕ n`, and the
last isomorphism identifies it, over `k`, with the rational function field
in the coordinates `n` over the rational function field in the
coordinates `m`. The module states this only in the scheme form above.

## Provenance

The provenance is internal and derived. The constructions use Mathlib's
affine-space universal property (`homOfVector`, `hom_ext`, `map`,
`isPullback_map`), its generic-point and stalk API, and its preimmersion
theory. No external theorem is asserted. This module does not prove
unirationality of any scheme; it supplies coordinate bookkeeping for
generic-fiber arguments.
