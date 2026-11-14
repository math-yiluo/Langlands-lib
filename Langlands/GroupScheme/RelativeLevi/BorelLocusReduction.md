# Geometric-fibre and étale-local reductions for the Borel locus

Workers 597 and 647. The internal proposition
`RelativeBorelLocusClopenReductionStatement` states that affine étale split
maximal-torus charts imply clopenness of the Borel locus. The supporting lemmas
combine the Borel-locus transport and weight-recognition interfaces. The final
theorem proves the exact
`RelativeBorelLocusClopenStatement` conditional on
`RelativeParabolicSplitMaximalTorusChartStatement`; this module does not prove
the chart-existence statement.

This is a derived logical reduction from the stated Library interfaces, with
no additional literature assertion. Acceptance of this unit leaves the
unconditional host target open until the chart-existence premise is proved.

`isGeometricBorelSubgroup_residueFiber_iff` identifies the residue-field
geometric Borel condition with Borelness on the actual chosen geometric fibre.
Naturality of `Descent.pullbackComparison` compares the successive residue-field
and algebraic-closure pullbacks with the composite geometric pullback. In the
reverse direction, reductivity gives the affine residue ambient group and
relative parabolicity gives the closed residue inclusion, so published
geometric Borel descent supplies the ground-field condition as well.

`isOpen_of_etale_local_preimage` and `isClopen_of_etale_local_preimage` detect
openness and clopenness on a pointwise family of étale charts. The chart need
only contain a point above the specified base point. Since an étale map is
open, the image of the open preimage is an open neighbourhood contained in
the set. Applying this to the set and its complement proves clopenness.
No surjectivity of any individual chart is assumed.

`isClopen_borelLocus_of_etale_charts` combines this topological argument with
`borelLocus_baseChange`. Thus clopenness of the actual Borel loci of the
base-changed relative parabolics implies clopenness on the original base.

On an arbitrary affine base, `borelLocus_eq_noOppositeWeightRankLocus` assumes
relative parabolicity, ambient reductivity, and a homomorphism from a standard
split torus whose composite into the ambient group is maximal on every chosen
geometric fibre. Relative parabolicity supplies the smooth and affine source.
At each point, the first comparison above replaces the residue-field geometric
Borel predicate by Borelness of the chosen geometric-fibre inclusion.
Reductivity and parabolicity persist on that fibre. The defining split-torus
base-change isomorphism identifies the composite of the geometric torus map
and the geometric subgroup inclusion with the map in the maximality
hypothesis. The field theorem
`splitTorus.isBorelSubgroup_iff_no_opposite_exponent_weight_finranks` therefore
identifies Borelness with exactly the predicate defining
`splitTorus.noOppositeWeightRankLocus`, using its actual geometric weight
spaces. There is no change of fibre models or freely supplied rank data.

`isClopen_borelLocus_of_splitMaximalTorus` applies that equality and the clopen
weight-rank-locus theorem. Neither theorem needs a separate closedness
assumption for the torus map: geometric maximality of its ambient composite
is the hypothesis used by field recognition.

Finally, `relativeBorelLocusClopen_of_splitMaximalTorusCharts` takes the chart
statement as its only premise. For each point of the arbitrary base, it selects
the statement's affine étale chart and point above the given point, pulls back
reductivity and relative parabolicity, and applies the affine clopen theorem.
The étale descent theorem then proves clopenness of the original Borel locus,
which is definitionally the set in the unchanged target statement. The
construction is universe polymorphic and imposes no extra base hypotheses.
