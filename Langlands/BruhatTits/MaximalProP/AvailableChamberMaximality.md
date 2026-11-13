# Maximality of positive subgroups of chambers

This internal construction concerns an actual supplied `KPBuildingDatum D` over a
nonarchimedean local field in an arbitrary universe `u`. The maximality results assume
`D.SatisfiesGroupAxioms`, all three `FacetReductiveComparisons D`,
`FiniteFieldSylowBorelStatement.{u}`, and the pro-p property of every actual facet positive
subgroup. These structural inputs remain explicit hypotheses. The construction does not
prove the availability-only `AvailableMaximalProPStatement`.

The first helper proves that the actual rational-point group of a connected reductive
locally finite-type affine group scheme has trivial modular character. It applies the
published central-derived-product proof of triviality of the adjoint determinant and the
published affine-point modular-character theorem. The rational-point continuous group
equivalence transports the result to the canonical rational-point topology. Local
compactness and Hausdorffness of the affine-point group are transported through this
same equivalence. No cocharacter or unimodularity premise is added.

For a pro-p subgroup contained in a chamber's zero fixer, the neutral-points axiom places
it in the actual neutral integral-point image. The first facet comparison identifies the
chamber's reductive quotient as a torus. The actual reduction image is a p-group by the
proved depth-zero reduction lemma, and the published torus theorem makes it trivial.
The reduction-kernel identity then puts the subgroup in the chamber's positive subgroup.
Thus the chamber positive subgroup contains every pro-p subgroup of its fixer whenever
the stated inputs hold.

If an element conjugates one chamber fixer to another, its conjugation also transports
their positive subgroups: both positive subgroups are pro-p by the explicit hypothesis,
and the largest-pro-p property just proved supplies the two inclusions, using inverse
conjugation for the reverse inclusion. The separately constructed chamber-fixer
conjugator therefore supplies a conjugator in the actual zero subgroup for any two
chamber positive subgroups. This argument uses fixer conjugacy and does not assume
covariance of the supplied integral models.

Containment between two chamber positive subgroups is equality. Both are compact and
open in the canonical rational-point topology. They are conjugate, and the actual ambient
group is unimodular by the first helper. The generic Haar-measure lemma excludes proper
containment of a compact open subgroup in a conjugate: their Haar volumes agree, and a
nonempty open difference would have positive measure. The proof installs the Borel
measurable structure only for this measure argument.

For a pro-p overgroup of a chamber positive subgroup inside the zero subgroup, the
chamber-containment construction gives a second chamber positive subgroup containing
that overgroup. The previous equality forces the overgroup to equal the original
positive subgroup. Together with the proved containment in the zero subgroup, openness
and the explicit pro-p input, this proves `IsMaximalOpenProPIn` for every chamber positive
subgroup.

The entry definition `maximalProPSubgroupContaining` takes any pro-p subgroup of the
zero subgroup, uses `proPSubgroupContainingChamber` to choose a containing chamber, and
returns its actual positive subgroup with both its containment and maximal-open-pro-p
certificates. No openness of the starting subgroup is required. The choice is not
asserted to be canonical or unique. The definition is a derived adapter of the actual
fixed-facet, chamber-containment, fixer-conjugacy, torus-reduction, modular-character and
Haar results. Classification of all maximal subgroups by unique chambers, their
normalizers, and discharge of the structural inputs remain separate obligations.
