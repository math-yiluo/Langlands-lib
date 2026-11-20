# Discrete-series comparison on the actual standard Levi

`rationalSemistandardStandardDiscreteSeriesComparison_of_borel` proves
`RationalSemistandardStandardDiscreteSeriesComparison` with independent field
and representation universes. At every standard index the two split-component
presentations give quotient measures on the same literal Levi. The target
requires each of the two independently supplied measurable structures there to
be Borel for its quotient topology. The equivalence compares the discrete-series
predicates of the same `SmoothDualClass` for the two Haar measures.

`RationalSemistandard.splitCenterChoiceIndependence` identifies the two
split-center point subgroups by applying it to `chosenLeviModel` at the
standard index and `standardLeviModel`. The standard model's subgroup is
definitionally `rationalLeviSplitCenter`. The centrality proofs are
`LeviModel.splitCenter_le_center` and `rationalLeviSplitCenter_le_center`.

`isClosed_standardLeviPoints` gives local compactness of the literal Levi
as a closed subgroup of the locally compact rational-point group.
`rationalPoint_secondCountableTopology` supplies second countability of
the ambient group, which passes to the Levi by its subtype embedding.
With these instances, `isDiscreteSeriesClass_borel_quotient_eq_iff`
substitutes the subgroup and Borel measurable-space equalities. The resulting
quotient carries two Haar measures, so their positive scalar relation
gives the equivalence by `isDiscreteSeriesClass_smul_measure_iff`.

This is a derived comparison of the formal presentations of the actual Levi
and its split component in Waldspurger (2003), I.1, printed pp. 238–239
(PDF pp. 4–5, `waldspurger-2003-plancherel`).
