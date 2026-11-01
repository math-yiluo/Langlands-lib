# Normalized affine-local frames of actual deformations

Let `k : Type u` be any field, `X : Scheme.{u}` any scheme, and
`f : X ⟶ Spec k`. Let `L` be an actual line bundle on `thickening f`, with a
specified actual trivialization

```
e : pullback(closedPoint f, L.obj) ≅ structureModule X.
```

For every affine open `U` of `X`, `affineNormalizedFrame f U hU L e`
constructs a section of `L` on `projection f ⁻¹ᵁ U`. It is a frame on that
whole open (`affineNormalizedFrame_isFrame`), and its coefficient after
actual zero-section pullback and application of `e` is exactly one
(`reducedCoefficient_affineNormalizedFrame`). There is no separation,
quasi-compactness, finite-type, reducedness or smoothness assumption on `X`.

A frame uses the existing `Scheme.Modules.IsFrameOn` predicate: on every
smaller open, multiplication of the restricted frame by ring sections is
a bijection onto the sections of the actual module sheaf. The construction
does not substitute a coefficient module for `L`.

## The restricted actual zero section

`closedPoint_preimage_projection` identifies the inverse image of
`projection f ⁻¹ᵁ U` under the actual zero section with `U`.
`closedPointOpen f U` is the actual `resLE` restriction from `U.toScheme`
to `(projection f ⁻¹ᵁ U).toScheme`.

Its composite with the open's inclusion agrees with the original zero
section after `U`'s inclusion. Its composite with the actual restricted
projection is the identity on `U.toScheme`. On underlying points the
restricted projection also supplies a preimage of every point of the
thickened open, by the already proved topological zero-section identity.
This proves `closedPointOpen_surjective`. The scheme identity supplies a
section of its actual global ring map, proving
`closedPointOpen_appTop_surjective`.

`zeroSectionOpenTrivialization` transports `e` to the local schemes using
the actual pullback composition and congruence isomorphisms, together with
the canonical pullback-of-structure-module isomorphism. For affine `U`,
the inverse-image open is affine because the actual projection is affine.
The two surjectivity facts allow the previously proved
`affinePullbackTrivialization` to construct `affineOpenTrivialization`.
The existing local frame theorem then proves `exists_affineOpen_frame`.

## Actual reduction of local sections

`reduceSection f U M s` first applies the actual pullback-adjunction unit
along `closedPoint f` to a section of `M` over the inverse-image open, then
restricts to `U` using the proved inverse-image equality. It is a section
of the actual pulled-back module on `U`.

For a specified trivialization `e` of that pulled-back module,
`reducedCoefficient f U M e s` applies `e` to `reduceSection`, producing
an actual ring section in `Γ(X,U)`. The scalar formulas prove

```
reducedCoefficient(a • s)
  = reductionMap(a) * reducedCoefficient(s).
```

Here `reductionMap` is the existing actual zero-section ring map. The
proof uses the actual pullback-local-section scalar formula, restriction
semilinearity and linearity of the actual module isomorphism `e`.

`reduceSection_naturality` and `reducedCoefficient_naturality` show that
both constructions commute with actual restriction to a smaller original
open. Their proofs use naturality of the actual pullback unit and of `e`,
with composition of restriction maps in the original presheaves.

## Normalization

If `s` is a frame on `projection f ⁻¹ᵁ U`, actual pullback carries it to a
frame on the zero-section inverse image. Restricting to `U` and applying
`e` gives a frame of the structure module. Its coefficient is a ring unit:
surjectivity of multiplication by that frame supplies an inverse.
This is `reducedCoefficient_isUnit`.

`isFrameOn_smul_unit` proves directly that multiplication of a frame by a
ring unit preserves the frame property. On each smaller open, the new
coefficient map is the composition of the original bijection with
multiplication by the restricted unit.

For a frame `s` with reduced coefficient unit `b`, multiply `s` by the
actual first-projection lift of `b⁻¹`. The frame property is preserved,
and its reduced coefficient is `b⁻¹*b = 1`, because actual reduction
retracts the first-projection ring map. This proves
`exists_normalized_frame_of_frame`. Applying it to the affine-local
frames proves `exists_affineOpen_normalized_frame`; the selected
`affineNormalizedFrame` retains both proved properties.

## Provenance and limits

This is an internal geometric construction. The local trivialization
argument uses the proved affine frame-lifting result and actual restricted
scheme morphisms. The local frame API and preservation of frames under
actual pullback are reused from the published FLT infrastructure without
modifying it. Normalization is proved using the actual zero-section ring
map and its projection splitting; no normalized-frame existence or
infinitesimal deformation classification is assumed.

The module supplies normalized frames on every chosen affine open. It
does not yet extract their additive transition cocycle or prove its
independence of choices, compare rigidified isomorphism classes with
right-derived cohomology, or prove the final tangent-to-H1 theorem.
