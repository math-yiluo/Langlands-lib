# Affine étale split maximal-torus charts for relative parabolics

`Langlands.GroupScheme.relativeParabolicSplitMaximalTorusCharts.{u}` proves
`RelativeParabolicSplitMaximalTorusChartStatement.{u}`. For every point of an
arbitrary base scheme, a relative parabolic in a reductive group has an affine
étale chart through that point and a closed homomorphism from a standard split
torus into the pulled-back parabolic. Its composite into the ambient group is
a maximal torus in every geometric fibre, with the source identified by the
canonical split-torus base-change isomorphism. The finite coordinate type and
all schemes and fields have the universe required by the statement.

## Evaluation and pullback comparisons

The private `evaluate_postcomp` lemma shows that evaluation of a relative Hom
commutes with postcomposition by the pulled-back original parabolic map.
`maximal_evaluate_iff` compares maximality of an evaluated homomorphism with
maximality of its raw base change. Both the commutative torus and the ambient
group are transported through `Descent.pullbackComparison`.
`maximal_coordinate_evaluate_iff` also removes the canonical coordinates
identifying a pulled-back standard split torus with the standard split torus
over the new base. These comparisons retain the actual homomorphisms and the
Library's `IsMaximalTorus` predicate.

## A smooth affine family through a geometric point

The private `exists_smooth_affine_parabolic_torus` starts with the chosen
algebraically closed geometric fibre. Relative parabolicity gives a parabolic
subgroup in the connected reductive fibre. `parabolicMaximalTorus` supplies a
maximal ambient torus factoring through this parabolic. Finite-Galois splitting
over the algebraically closed field identifies that torus with a standard split
torus. Closedness of the map into the parabolic follows from closedness of its
composite into the ambient fibre.

Smooth representability of Hom from a split torus to the smooth affine
parabolic then realizes this homomorphism as the evaluation of a universal
family at a point of a smooth parameter scheme over the original base.
The private `exists_affine_closed_evaluations` shrinks this parameter scheme
twice, using the open closed-immersion locus, so that the evaluated torus map
into the parabolic and its composite into the ambient group are both closed
immersions. Both restrictions preserve the original field point. A further
affine open restriction gives a smooth affine map to the base and a lift of the
original geometric point. The evaluation comparisons transfer the original
maximality to the actual base-changed ambient torus map at this lift.

## The étale chart and all its geometric fibres

The final theorem applies the open geometric self-centralizing torus locus to
the closed ambient torus map on this smooth affine family. The initial
maximality places the lifted geometric point in that locus: ambient
reductivity supplies the identity-component reductivity condition, and the
published maximal-torus centralizer theorem supplies self-centralization.

Restrict to this open locus. The theorem on étale local sections of a smooth
morphism gives an affine étale chart whose image contains the specified point
of the original base. Pulling the torus map into the parabolic back to this
chart, composing with the target pullback comparison and the standard source
isomorphism, gives the required closed homomorphism. Naturality of the target
comparison identifies its ambient composite with the corresponding pullback
of the original ambient torus map.

Every geometric point of the chart maps into the self-centralizing open
locus. The reductive self-centralizing criterion gives maximality in the
associated geometric fibre, and residue-fibre reflection followed by the
field-point maximality comparison gives maximality at the actual composite
field point. Base-change composition and the target pullback comparison
transfer this to the chart's ambient group. The last standard split-torus
source isomorphism gives exactly the geometric-fibre homomorphism in the
statement.

## Provenance and scope

This is an internal derivation from the imported Library theorems, rather than
a new external-source assertion. The chart statement's paired Markdown records
its relation to Conrad's maximal-torus construction. The proof implemented here
uses smooth Hom families, two closed-immersion restrictions, the open
self-centralizing locus and étale local sections.

The only global group hypotheses are `IsReductive G` and
`IsRelativeParabolicSubgroup i`. No Noetherian or global torus assumption is
added. The proof uses closedness of the two torus maps on suitable open
neighbourhoods. Its pointwise étale charts provide the remaining premise of the
separate Borel-locus clopenness reduction.
