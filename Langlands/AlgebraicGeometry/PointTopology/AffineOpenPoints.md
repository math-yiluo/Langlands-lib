# Actual affine basic-open point comparisons

This unit constructs the homeomorphism from actual points of a basic open
subscheme of an affine scheme to the subtype of points whose entire image
lies in that open. It uses the existing affine evaluation topology on both
scheme-point spaces and proves that the inclusion is an open embedding when
units form an open subspace.

## Source and provenance

This is a derived relative comparison implementing the basic-open step in
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), Proposition 3.1 and its proof, printed page 4. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The preceding discussion characterizes points of a localization by a unit
condition and explains the inverse-continuity obstruction. The proof uses this
basic-open comparison before the separate local-ring open-cover argument.

The implemented comparison works for any affine object
`X : Over (Spec (CommRingCat.of R))`, with commutative rings `R` and `S` in a
common arbitrary universe and `Algebra R S`. Only `S` is topologized. The basic
open is taken at an element `f` of the actual global-section coordinate ring
`AffineCoordinateRing R X = Γ(X.left, ⊤)`.
There is no finite-type, finite-presentation, local-ring or separation
assumption. Continuity of multiplication on `S` suffices, together with the
specified hypothesis on its units. This weaker scope is a derived extension
of the source's basic-open argument: localization fractions use only
multiplication and continuous inversion on the unit space, and the comparison
uses already constructed evaluation topologies.

## Construction and exact maps

All public names lie in `Langlands.AlgebraicGeometry.PointTopology`.

The coordinate algebra of `openOver R X (X.left.basicOpen f)` is the actual
ring of global sections of that open subscheme. Local auxiliary instances use
the algebra structure supplied by the actual inclusion's map on global
sections, and Mathlib's `Γ_restrict_isLocalization` proves that this algebra
is a localization away from `f`. Coordinate-pullback naturality proves
compatibility with the specified `R`-algebra structures. These instances
introduce neither a new coordinate ring nor a new global point topology.

The private lemma `basicOpenPointMap_factor` identifies the actual
`openPointMap` exactly with the composite of the source scheme-point
homeomorphism, precomposition by this localization algebra map, and the inverse
target scheme-point homeomorphism. Thus the comparison is about the actual
postcomposition map of relative scheme morphisms.

`isEmbedding_basicOpenPointMap` assumes `ContinuousMul S` and an explicit
`hS : IsEmbedding (Units.val : Sˣ → S)`. It transports the localization-point
embedding from `Localization` along that exact factorization. Mathlib's unit
topology records both the value and inverse value, so this hypothesis expresses
that it is the subspace topology; it is not inferred for arbitrary topological
rings.

`basicOpenPointHomeomorph R X S hS f` has source
`RingPoint R (openOver R X (X.left.basicOpen f)) S` and target the subtype
`{p : RingPoint R X S // Set.range p.left ⊆ X.left.basicOpen f}` with its
subspace topology. Its underlying equivalence is the already constructed
`openPointEquiv`; its map is exactly postcomposition with the actual open
inclusion, as `basicOpenPointHomeomorph_apply` proves. The embedding just proved
makes this existing equivalence a homeomorphism. Its inverse is therefore the
actual open-immersion lift, with no new presentation of points.

`isOpenEmbedding_basicOpenPointMap` assumes `ContinuousMul S` and
`IsOpenUnits S` and proves that this same point inclusion is an open embedding.
`IsOpenUnits` says that the unit inclusion with its existing value-and-inverse
topology is an open embedding. The proof transports the principal-localization
open embedding along the same exact scheme-point factorization.

This unit uses the separately staged `SchemePoints` and `Localization` pairs
unchanged. It establishes the basic-open construction, not the general affine
open or nonaffine chart-gluing theorem. Localness is still required at the
later open-cover step, and the other conclusions of Proposition 3.1 remain
separate obligations.
