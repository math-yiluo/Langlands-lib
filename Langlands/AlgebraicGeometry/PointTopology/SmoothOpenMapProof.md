# Proof: smooth morphisms are open on local-field rational points

Author: Worker 1505.

`Langlands.AlgebraicGeometry.PointTopology.smoothRationalPointOpenMap` proves the
published proposition `SmoothRationalPointOpenMapStatement.{u}` of
[SmoothOpenMapStatement](SmoothOpenMapStatement.md) for every universe `u`.
That is: for a nonarchimedean local field `F`, affine `X` and `Y` over `Spec F`,
and `f : X ⟶ Y` with `Smooth f.left`, postcomposition with `f` is an open map
`RationalPoint F X → RationalPoint F Y` for `rationalPointTopology`. There is
no characteristic, finite-type or nonemptiness restriction.

## Helper declarations

- `affineRationalPoint_natural`: for any commutative ring `R` and morphism
  `f` of affine schemes over `Spec R`, the composite of
  `rationalPointEquiv` and `affineSchemePointEquiv` carries `p ↦ p ≫ f` to
  `AlgPoint.precomp (affineCoordinatePullback R f)`. It is the published
  `rationalPointEquiv_natural` followed by `affineSchemePointEquiv_natural`.
- `affineRationalPointHomeomorph R X`: the composite homeomorphism
  `(rationalPointHomeomorph R X).trans (affineSchemePointHomeomorph R X R)` from
  `RationalPoint R X`, with `rationalPointTopology`, to
  `AlgPoint R (AffineCoordinateRing R X) R`. Its underlying function is the
  composite of the two equivalences (`affineRationalPointHomeomorph_apply`, by
  `rfl`). The topology is the published one; the homeomorphism only records
  the existing transport.
- `smooth_affineCoordinatePullback`: if `Smooth f.left` and both underlying
  schemes are affine, then the ring map of `affineCoordinatePullback R f`, which
  is `f.left.appTop.hom` by definition, is `RingHom.Smooth`. This is Mathlib's
  `HasRingHomProperty.iff_of_isAffine` for the property `Smooth`.
- `isOpenMap_precomp_of_smooth_localField`: over a nonarchimedean local field
  `F`, restriction of `F`-points along a smooth map of `F`-algebras in
  `Type u` is open. The proof installs the Library's canonical
  `Langlands.LocalGalois.localNormedField F`, whose topology is the given
  topology of `F` by the published `rfl` theorem `localNormedField_topology`,
  and its completeness `localNormedField_complete F`. It then applies
  `SubmersiveOpen.isOpenMap_precomp_of_smooth` from
  [SubmersiveOpenMap](SubmersiveOpenMap.md).

## Main proof

After introducing the data, the rational-point topologies are installed as in
the statement. By `isOpenMap_precomp_of_smooth_localField` and
`smooth_affineCoordinatePullback`, restriction along the coordinate pullback
of `f` is an open map of algebra points. By `affineRationalPoint_natural`, the
map `p ↦ p ≫ f` equals

```text
(affineRationalPointHomeomorph F Y).symm ∘ AlgPoint.precomp (affineCoordinatePullback F f)
  ∘ affineRationalPointHomeomorph F X.
```

Homeomorphisms are open maps, and composites of open maps are open.

The mathematical content is in the helper module
[SubmersiveOpenMap](SubmersiveOpenMap.md). Smooth ring maps are locally standard
smooth on a principal-open cover of the source, and principal opens give open
embeddings of points. For a finite submersive presentation, Mathlib's inverse
function theorem is applied to the relations, with their finitely many
coefficients as additional parameter coordinates. Points of the target near a
given restriction therefore lift to nearby points of the source.

The theorem is split into the helper lemmas above, rather than proved in one
tactic block, so that the kernel checks the local-field normed instance and the
rational-point transport separately. A single combined proof timed out in
kernel checking.

## Provenance

This is the affine nonarchimedean case of the openness of smooth maps on
`K`-points, stated in Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed p. 11 (paragraph introducing Theorem 4.5).
That paragraph sketches a proof via étale maps and continuity of simple roots.
The implemented route instead applies the inverse function theorem to a local
standard-smooth presentation; see the helper module.
