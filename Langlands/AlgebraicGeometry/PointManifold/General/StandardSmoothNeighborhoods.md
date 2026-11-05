# Universe-general standard-smooth principal neighborhoods on actual affine points

This module adapts the published `PointManifold.StandardSmoothNeighborhoods` implementation by Worker 135
to `PointManifold.General`, with an explicit arbitrary coefficient universe
`u` and `k : Type u`. Worker 1650 made this universe extension. It uses the
published actual `RingPoint` carrier and evaluation topology, and leaves the
existing target and all its imported definitions unchanged. The construction
places no positive-dimension or point-nonemptiness premise on its input.

This internal helper supplies the algebraic neighborhood step for regular chart
existence. For a field `k`, an affine scheme `X` over `Spec k`, and algebraic
`SmoothOfRelativeDimension d X.hom`, `exists_standardSmooth_basicOpen` proves that
every scheme point `x` belongs to a principal open `D(f)` for a global regular
function `f`, and that the actual affine coordinate algebra of that open is
standard smooth over `k` of relative dimension `d`. It does not assume a
real or complex structure, and its conclusion supplies no analytic charts.

`StandardSmoothPrincipalNeighborhood k X d x` records the chosen global
function, membership of `x` in its principal open, and standard smoothness of
that open's actual coordinate algebra. The choice constructor
`standardSmoothPrincipalNeighborhood` obtains this record from algebraic
smoothness using the existence theorem. The record can be used without a
smoothness assumption on the original scheme; only its constructor requires
that assumption.

The preliminary lemma `affineCoordinateMap_eq_appTop` identifies the published
affine coordinate algebra structure map with pullback on global sections
composed with the canonical `k ≅ Γ(Spec k, ⊤)`. Its proof uses full faithfulness of
`Spec` and naturality of the spectrum/global-sections comparison.
`standardSmooth_coordinateRing_of_appTop` transports fixed-dimension standard
smoothness along this ring isomorphism. `openOver_appTop` identifies the global
pullback for an open subscheme with `appLE` followed by the canonical isomorphism
between sections on the open and global sections of its associated scheme.
The latter identity is valid without affineness.

The main proof starts with the neighborhoods in Mathlib's definition of
`SmoothOfRelativeDimension`. It applies
`exists_basicOpen_le_appLE_of_appLE_of_isAffine` to refine both neighborhoods
inside the whole affine source and target. This refinement preserves the fixed
relative dimension by stability under localization away from one element.
The target principal open contains the image of `x`; since `Spec k` has a
subsingleton underlying space, that open is all of `Spec k`. The proof then
transports standard smoothness through the canonical top-section isomorphism
of the source open and through `Γ(Spec k) ≅ k`. This produces the coordinate
algebra used by the existing actual-point topology, rather than introducing a
different algebra structure.

These are internal derived results from the pinned Mathlib scheme, localization,
and standard-smoothness APIs and the published `PointTopology` coordinate
definitions. Their provenance is this compatibility construction, not a
transcription of an external theorem.
