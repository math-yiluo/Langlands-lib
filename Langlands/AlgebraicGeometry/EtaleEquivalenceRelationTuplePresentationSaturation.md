# Images and saturations of symmetric tuple charts

This is derived infrastructure for the filtration by symmetric tuple charts
in Stacks Project, Lemma 68.8.3 (Tag 0BBN), and its finite version in Lemma
68.8.6 (Tag 07ST). The registered originals are
`stacks-stratification-2026-11-02` and
`stacks-noetherian-approximation-2026-11-01`. An index `n` denotes `n+1`
entries. Schemes live in arbitrary universe `u`. All declarations assume
that the original source is separated. From the symmetric cross image
theorem onward, the original object and arrow schemes are affine. The
finite presentation and cover results also assume that the original joint
endpoint map is a closed immersion.

`exists_tupleCross_point` constructs an underlying point of the ordered
cross-correspondence over two ordered tuples whose zeroth coordinates
are related. Two applications of the scheme pullback point-existence
theorem supply a point in the nested pullback. This step includes the
necessary residue-field extensions; it does not identify scheme
pullback carriers with set-theoretic pullbacks.

`tupleSymmetricCrossLeft_range` identifies the image of the first endpoint
of the symmetric cross-correspondence of lengths `m` and `n` with the
`n`th threshold on the `m`th chart. One inclusion follows from threshold
invariance along cross-correspondences and the self-threshold formula.
For the other, lift a symmetric point to an ordered representative,
unpack its threshold membership as a related point in the ordered tuple
image, construct an ordered cross point, and pass to its symmetric
quotient.

`tupleChartObjectι_saturation` identifies the open saturation of a
component in any finite tuple presentation with the total threshold at
that component's length. One inclusion uses invariance of the total
threshold. For the reverse inclusion, decompose the target point into a
coproduct component and use the symmetric cross image theorem to
construct an actual arrow from the selected component.

`tupleChartReindexObjectMap_saturation` treats a selected finite subfamily
whose lengths are all at least `d` and which contains a chart of length
`d`. Provided its object map is an open immersion, the saturation of its
open image is precisely the `d`th total threshold. The upper inclusion
uses threshold preimages, the full-threshold formula on the subfamily,
and invariance. The lower inclusion uses the component of length `d`,
the component inclusion equation, and monotonicity of saturation.
`tupleTailToTailObjectMap_saturation` specializes this to the inclusion
from the tail starting at `q` into the tail starting at `p`, under
`p ≤ q < N+1`. `tupleTailObjectMap_saturation` gives the corresponding
formula for the tail inside the whole finite presentation, under
`p < N+1`.

`tupleTailCrossCoverScheme N p q hpq`, for `hpq : p ≤ q`, is the
scheme pullback of the lower-tail source map along the higher-tail object
inclusion. A point has a lower-tail arrow together with a lift of its source
to the higher tail. `tupleTailCrossCoverSource` is that chosen source lift;
`tupleTailCrossCoverArrow` is the underlying lower-tail arrow;
`tupleTailCrossCoverTarget` is its lower-tail target. The two
`tupleTailCrossCoverArrow_s` and `_t` equations give the endpoint composites.
The cover scheme is affine because it is a pullback of affine schemes.
Its source map is etale by base change of the lower-tail source. The arrow
map is an open immersion by base change of the higher-tail inclusion,
and its composite with the etale lower-tail target is etale.

`tupleTailCrossCoverTarget_range`, assuming also `q < N+1`, identifies
the target image with the `q`th threshold on the lower-tail object scheme.
The preceding saturation formula reduces this to the image of all arrows
whose source lies in the higher-tail image. One inclusion uses the actual
arrow and its source lift. In the reverse direction, a point in the
saturation supplies an arrow and a chosen higher-tail source point; the
scheme pullback point-existence theorem supplies a point of the cover
with the prescribed arrow. Residue-field extensions are again included.

`tupleTailThresholdCover` factors that target map through the threshold
open using its image formula and the lifting property of open immersions.
The equation `tupleTailThresholdCover_ι` identifies the composite with
the original target. The factor is etale by cancellation against the
open immersion. It is surjective: the target image formula lifts every
threshold point, and injectivity of the open inclusion identifies the
lift with that point. Thus this is an actual affine scheme with a
surjective etale morphism onto the invariant threshold open.

These are image and covering statements for the existing presentations;
they assert no approximation theorem.
