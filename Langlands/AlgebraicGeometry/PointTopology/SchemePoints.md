# Affine-chart final topology on actual scheme points

This unit constructs a named topology on actual relative scheme points using all
actual affine open charts and their existing affine evaluation topologies. It
also constructs the open-subscheme point equivalence, proves the local-ring
coverage criterion, and proves agreement with the existing affine topology.

## Source and provenance

This is a derived construction from the gluing argument in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Proposition 3.1 and its proof, printed page 4. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The paper observes that over a local value ring every point factors through
some member of any open cover, then glues the affine point topologies under
additional open-unit and inversion hypotheses. This unit constructs the final
topology and the coverage step explicitly on the existing scheme-point carrier.

The relative base ring `R` and value ring `S` are commutative rings in a common
arbitrary universe, and `S` is an `R`-algebra. The target is an arbitrary object
`X : Over (Spec (CommRingCat.of R))`. Only `S` has a topology. No finiteness,
separation or topology hypothesis on `R` is needed. Defining a final topology
and proving its affine comparison requires no local-ring or open-unit
hypothesis. The coverage results separately assume `IsLocalRing S` and do not
require a topology on `S`. Allowing arbitrary schemes and value rings here is
a derived extension of this construction, not an assertion of all properties
in the proposition outside its stated hypotheses.

## Actual open-subscheme points

All declarations lie in `Langlands.AlgebraicGeometry.PointTopology`.

- `openOver R X U` is the actual open subscheme `U` with structure map
  `U.ι ≫ X.hom`. `openOverι` is its inclusion as a relative scheme morphism.
- `openPointMap` is actual postcomposition with this inclusion on
  `RingPoint R (openOver R X U) S`. It is injective because the open immersion
  is a monomorphism.
- `openPointLift` factors a point through `U` when its entire underlying scheme
  image lies in `U`. `openPointMap_lift` proves the factorization identity.
- `openPointEquiv` identifies these open-subscheme points with the subtype of
  actual points whose entire image is contained in `U`. It uses the actual
  open-immersion lift and no choice of coordinates.
- `range_subset_open_iff_closedPoint` says that, for a local value ring, image
  containment is equivalent to the image of the unique closed point belonging
  to `U`. Every prime of a local ring specializes to the closed point;
  continuity and stability of opens under generalization prove the criterion.
- `exists_openPointMap_of_cover` proves coverage for any open cover indexed in
  an arbitrary universe. `exists_affineOpenPoint` specializes this to all
  affine opens, using an affine neighborhood of the closed-point image.

## The topology and implemented comparison

`schemePointTopology R X S` is the supremum of the topologies coinduced by
`openPointMap` from each affine open, whose source carries the existing affine
scheme-point topology from `AffineSchemeMaps`. It is a named topology; this
unit installs no competing global instance on scheme points.
`schemePointTopology_isOpen_iff` proves that a subset is open precisely when
its inverse image in every affine chart is open.
`schemePointTopology_continuous_chart` proves continuity of each chart map.
These follow directly from the final-topology construction and do not assert
that the chart maps are open embeddings.

`openOverTopIso` constructs the actual relative isomorphism from the top open
subscheme to `X`. For an affine target, `schemePointTopology_eq_affine` proves
equality with the existing affine evaluation topology. One inequality uses
coordinate-pullback naturality to prove that every affine chart map is
continuous in that topology. The top affine open supplies the reverse
inequality through the existing affine point homeomorphism of the actual
relative isomorphism. Thus the new construction uses the existing point
carrier and agrees exactly with the earlier topology when it applies.

The further open-chart and gluing comparisons, functoriality, uniqueness,
fiber-product compatibility, and nonaffine Hausdorff/local-compactness results
of Proposition 3.1 remain separate obligations. In particular this unit does
not assume those properties in a structure or claim them from the definition
alone. The source's local-ring, open-unit and continuous-inversion hypotheses
remain necessary at the corresponding later steps.
