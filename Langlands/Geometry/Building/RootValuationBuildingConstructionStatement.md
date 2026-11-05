# Actual root-valuation data with the metric-construction axioms

`Langlands.Geometry.Building.RootValuationBuildingConstructionStatement` is
a Prop-valued construction target at every universe `u`. It quantifies over
every nonarchimedean local field `F` and every actual connected reductive
group `G/F`, including equal and mixed characteristic. Its conclusion
constructs `P : ParahoricBuildingData G`, a polysimplicial realization `R`
and an apartment splitting `T`, together with the five axiom witnesses
required in the corrected opening of Kaletha–Prasad Section 4.2.

The underlying quotient and action are the existing ones associated to
`P.toValuationBuildingData`. Its torus is an actual maximal split torus of
`G`, its root groups are the actual relative root groups, and its apartment
is an equipollence class of valuations normalized by `localFieldOrder F`,
with the actual centralizer and V 6. All this data belongs to the
existential conclusion.

The conjunction in that conclusion retains the existing Library expressions
of the following source axioms:

| Source axiom | Constructed witness |
| --- | --- |
| 4.1.1, its one-group building clauses | `P.SatisfiesBuildingAxiom R` |
| 4.1.2 | `P.HasBoundedOpenStabilizers` |
| 4.1.4 | `P.SatisfiesAffineApartmentAxiom T` |
| 4.1.6, AS 1 through AS 6 | `P.HasRootReflections`, `P.SatisfiesApartmentAxioms`, and `P.HasCompatibleApartmentFacets` |
| 4.1.9 | `P.HasTitsSystem` |

In particular, the topology condition V 7 and AS 5 must be proved in the
constructed instance. They cannot be assumed to follow merely from the
existence of `ValuationBuildingData`. The topology appearing in the
bounded-open-stabilizer condition is the existing canonical
`rationalPointTopology F G.X`.

This is a derived subset of the general construction in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), with the authors' corrections
of 1 November 2024. Theorem 9.2.7, printed p.329 / PDF p.360, constructs
the descended building `B(G_K)^Γ`. Section 9.5, printed pp.363–364 /
PDF pp.394–395, assembles the axiom witnesses, including 4.1.2 and the
individual AS clauses. The statement here keeps only the five axioms
needed for the metric construction, rather than the full corrected
ten-axiom availability certificate.

The output must be data for the existing root-valuation quotient, so the
descended carrier alone is insufficient. Theorem 9.6.5 and §9.6.6, printed
pp.366–367 / PDF pp.397–398, give the additional source route: construct
the compatible valuation class for `(G,S)`, compare the affine roots and
the point fixers at every corresponding apartment point, and identify
the descended building with the building constructed from that class.
The latter is the quotient (7.6.2) in Remark 7.6.5, printed p.266 /
PDF p.297. A proof successor must establish these actual comparisons or
an equivalent direct construction on the existing quotient.

The corrections at PDF p.33 add AS 5 to the standing Chapter 7 premises
and explain its general proof through Proposition 9.4.35 over a perfect
residue field. At PDF pp.28–29 they add Axiom 4.1.6 to the metric
section and correct the comparison hypothesis of Corollary 4.4.5 to
range over every pair of corresponding apartment points. PDF p.39
repairs the finite-orbit and fixed-point steps in §9.2.1. These
corrections are part of the construction route. A nonarchimedean local
field has finite, hence perfect, residue field, so the target retains no
additional residue-field or characteristic restriction.

The internal scope was chosen to provide exactly the actual data and
witnesses consumed by the separate
`Langlands.Geometry.Building.MetricRealizationStatement`. This module
does not import that target or assert its proof. Worker 118 proposed
the reusable actual-data and metric prerequisite boundary; Worker 1681
formulated this five-axiom construction specialization and authored
the Lean and Markdown.

No proof of the proposition is supplied here. In particular, this
statement supplies no constructed building, no metric, no canonical
model family and no comparison with a supplied integral model. A proof
of this five-axiom target would not by itself establish the full
corrected availability predicate. The unchanged
`IntegralModel.BuildingComparisonStatement` still requires the metric,
the original supplied-model image comparison, a special vertex, its
exact norm-kernel stabilizer identity and unique fixation.
