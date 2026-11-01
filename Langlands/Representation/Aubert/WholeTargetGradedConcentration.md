# Concrete whole-target graded concentration

Authors: Worker 194 and Worker 164.

This internal prerequisite constructs the whole-target interval data required
by the signed geometric comparison and proves lower concentration for each
actual singleton support grade. Its inputs are the actual target Jacquet
block bound, membership of the removed permutation in the upper support, and
strict inversion-length upper closure of the upper and lower supports. The
coefficient is an actual flattened Jacquet module of the original
representation, rather than an independently supplied constant module.

The existing `intersectionSource_eq_of_intersectionTarget_eq` and
`wholeTarget_flattened_eq` in
[`CorrectedOrbitCoefficientCutComparison`](CorrectedOrbitCoefficientCutComparison.md)
supply the subgroup and common-shape comparisons. The subgroup argument
shows that a whole target intersection
makes the source intersection the conjugation pullback of the entire target
subgroup. The flattened actual source refinement has that Weyl subgroup.
Since standard block Weyl subgroups determine their ordered block shapes,
all whole-target source refinements flatten to the same shape.

When the inverse permutation is increasing on target blocks and maps uncut
target edges to adjacent increasing edges, the source cuts form the Boolean
interval between the permutation descents and the allowed inverse images.
The lower endpoint lies in the interval. The construction chooses actual
standard intersection refinements at every active cut set and takes the
common flattened shape from the refinement at this lower endpoint. The
actual core criterion supplies support activity and source minimality; the
whole-target interval theorem supplies the target intersection equality;
the preceding flattening argument supplies the same coefficient at every
active coordinate. Outside the interval the actual quotient vanishing
proved in `CorrectedWholeTargetInterval` supplies the required zero objects.
Thus every field of `WholeTargetIntervalData` is constructed here.

The existing signed comparison applies the actual coherent orbit integral,
whole-target evaluation, and common flattened Jacquet quotient comparison
at each coordinate. Its all-class naturality square preserves the actual
quotient cut maps and every exterior insertion sign. It identifies the
actual graded diagram with `WholeTarget.diagram` for the constructed common
Jacquet coefficient.

The signed Boolean interval complex is exact below its largest allowed
degree, whose value is the target block count minus one. Its initial map is
injective if this target degree is positive. Transport through the signed
diagram equivalence proves those conclusions for the actual graded
quotient diagram. If either fixed inverse-permutation condition fails,
every coordinate actual quotient is zero, hence every homogeneous product
is zero and the same lower conclusions follow. No extra geometric-data
premise remains in the exported concentration theorems.

All ranks, including zero and the empty Levi, are retained. The field and
representation universes remain independent, and the carrier is saturated
as required by the target Jacquet block bound. This result asserts neither
exactness at the surviving target degree nor exactness of a full complex
ending in zero. Finite filtration, upper-degree vanishing, and the final
Grothendieck class/effectivity comparison are downstream obligations.

Provenance is internal. Worker 194 supplies the concrete active interval,
common-shape argument and concentration transport; Worker 164 supplies the
actual bundled signed comparison used by this construction.
