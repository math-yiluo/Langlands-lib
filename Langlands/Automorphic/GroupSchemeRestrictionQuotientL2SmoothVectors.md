# Smooth vectors in `L²([G])` and their transport along `quotientL2Equiv`

Author: Worker 112.

The published module `GroupSchemeRestrictionQuotientL2InfiniteAction`
restricts the right action on `L²` of the restriction split-centre quotient
`RestrictionSplitCentre.Quotient F G S j` to the infinite adelic points. This
quotient has the shape `[G] = A_G G(F) \ G(A_F)` of Getz--Hahn (2.20)--(2.21)
(`getz-hahn-2024-automorphic-representations`, printed pp. 68--69). The
published `rationalQuotientL2FiniteRightAction` restricts the same action to
the finite adelic points.

The present module names the finite-smooth and the simultaneously smooth
vectors in `L²([G])` as submodules. It also proves that the published isometric
equivalence `quotientL2Equiv` with the positive-torus quotient `L²` identifies
smooth vectors of both kinds. Consequently density of smooth vectors holds on
one side exactly when it holds on the other. No density is proved.

## Generic intertwining lemmas

Let `Γ` be a group with a topology and a charted space structure over a model
`I` with corners over `ℝ`. Let `E`, `E'` be complex normed spaces with actions
`π`, `π'` of `Γ` by bounded operators.

- `isSmoothVector_of_intertwining`: if a bounded linear map `L : E → E'`
  satisfies `L (π g v) = π' g (L v)`, then `L` maps real smooth vectors
  (`Langlands.Archimedean.IsSmoothVector I`) to real smooth vectors. The orbit
  map of `L v` is `L` composed with the orbit map of `v`, and a bounded real
  linear map is `C^∞`.
- `isSmoothVector_linearIsometryEquiv_iff`: for an intertwining linear
  isometric equivalence `L`, the vector `L v` is real smooth exactly when `v`
  is. The inverse also intertwines.

Let `R` be a commutative ring, `Γ` a group with a topology (no continuity of
the group operations is needed), and `ρ`, `ρ'` representations of `Γ` on `R`-modules `V`, `V'`.

- `isSmoothVector_of_finiteIntertwining`: an intertwining linear map carries a
  vector fixed by an open subgroup `K` (`Langlands.IsSmoothVector`) to a vector
  fixed by the same `K`.
- `isSmoothVector_linearEquiv_iff`: for an intertwining linear equivalence
  `L`, the vector `L v` is fixed by some open subgroup exactly when `v` is.

## Submodules of `L²([G])`

Here `F : Type` is a number field, `G` is a group scheme over `Spec F` whose
underlying scheme is affine and locally of finite type, `S` is a commutative
group scheme over `ℚ` with `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G`,
`measureQ` is any measure on `Quotient F G S j`, and
`hInv : QuotientRightInvariant F G measureQ`.

- `rationalQuotientL2FiniteSmoothVectors F G measureQ hInv` is the complex
  submodule of `Lp ℂ 2 measureQ` of classes fixed by some open subgroup of the
  finite adelic points under `rationalQuotientL2FiniteRightAction`. The open
  subgroup `⊤` fixes `0`, and `K ⊓ K'` fixes a sum. Membership is unfolded by
  `mem_rationalQuotientL2FiniteSmoothVectors`.
- For a model `I` and any charted space structure on the infinite adelic
  points, `rationalQuotientL2BiSmoothVectors F G measureQ hInv I` is the
  intersection of the published `Langlands.Archimedean.smoothVectors I` of
  `rationalQuotientL2InfiniteRightAction` with the finite-smooth submodule.
  Membership is unfolded by `mem_rationalQuotientL2BiSmoothVectors`.

## Transport along `quotientL2Equiv`

From here on the measure on `[G]` is the canonical
`quotientHaarMeasure F G S j`, with any proof `hInv'` of its right invariance.
In addition `T` is a commutative group scheme over `F` with
`i : T.toGrp ⟶ G` and `h : subgroup F G S j = imageSubgroup F T G i`. Also
`characterRestrict i` is injective (`hi`) with finite-index range,
`hc : IsCentral i`, Haar measure on `normOneSubgroup F G` is right invariant
(an instance argument), and `Iₛ`, `e` are splitting coordinates of `T`. On the
positive side the measure is `positiveRationalQuotientHaarMeasure F G T i`,
and the actions are the published `haarQuotientL2InfiniteRightAction` and
`haarQuotientL2FiniteRightAction`.

- `quotientL2Equiv_finiteRightAction`: `quotientL2Equiv F G h` carries the
  positive-torus finite action of `b` to `rationalQuotientL2FiniteRightAction`
  of `b`. This is the published `quotientL2Equiv_rightAction` at
  `ofFinite b`.
- `isSmoothVector_quotientL2Equiv_iff`: for any model `I` and charted space
  structure on the infinite adelic points, a positive-torus class is real
  smooth for the positive infinite action exactly when its image is real
  smooth for the infinite action on `L²([G])`. It uses the published
  `quotientL2Equiv_infiniteRightAction`.
- `isFiniteSmoothVector_quotientL2Equiv_iff`: the same for being fixed by some
  open subgroup of the finite adelic points.
- `image_quotientL2Equiv_smoothVectors`: the image under `quotientL2Equiv` of
  the positive real smooth vectors is the set of real smooth vectors of
  `L²([G])`.
- `image_quotientL2Equiv_biSmoothVectors`: the image of the positive classes
  that are real smooth and finite smooth is
  `rationalQuotientL2BiSmoothVectors`.
- `dense_smoothVectors_iff` and `dense_biSmoothVectors_iff`: the real smooth
  vectors, respectively the simultaneously smooth vectors, are dense in
  `L²([G])` exactly when the positive-torus ones are dense in the positive
  quotient `L²`. A homeomorphism maps dense sets onto dense sets.

The density sets on the positive side are written exactly as in the conclusion
of the published `GroupSchemeQuotientL2SmoothDensityStatement` of Worker 116.
With the connected-reductive atlas `reductiveChartedSpace`, these equivalences
reduce a `[G]` density statement to the positive one. That reduction is not
carried out here.

## Scope

No connectedness, reductivity or manifold structure is assumed; the atlas on
the infinite adelic points is an arbitrary instance argument. The module proves
no density of smooth vectors, no pointwise smoothness of representatives and
no finite volume, admissibility or spectral statement.

## Provenance

This is internal bookkeeping on the published `L²([G])` actions and the
published comparison with the positive-torus quotient. The proofs use the
published `quotientL2Equiv_rightAction` and
`quotientL2Equiv_infiniteRightAction`, and Mathlib's
`ContinuousLinearMap.contDiff`, `Representation.mem_invariants` and
`Homeomorph.isDenseEmbedding`. No external theorem is asserted.
