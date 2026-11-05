# A metric-construction target on the actual KP quotient

This module defines `ValuationBuildingData.MetricRealization` and the
Prop-valued target `Langlands.Geometry.Building.MetricRealizationStatement`
at every universe `u`. It supplies no proof of that target and constructs no
metric.

For supplied `B : ValuationBuildingData G`, a `B.MetricRealization` consists of
a `MetricSpace` and a `CompleteSpace` on the existing type
`B.ReducedBuilding`, the midpoint nonpositive-curvature condition
`Langlands.Geometry.Metric.KP.IsNonpositivelyCurved` for that metric, an
`IsIsometricSMul` instance for the existing action of `rationalPoints G`, and
continuous orbit maps. The group topology in the last field is exactly
`rationalPointTopology F G.X`. The topology of the quotient is the one induced
by the chosen metric. Neither the quotient nor its action is replaced.

The predicate uses the NPC definition already in the Library. It asserts
existence of a point satisfying the squared-distance midpoint inequality for
each pair of points; it does not hide geodesic existence or completeness.
Completeness is a separate field of the realization. No normalization of the
metric on simple factors is prescribed.

The statement fixes a nonarchimedean local field `F`, an actual connected
reductive group `G/F`, and supplied `P : ParahoricBuildingData G`, a
polysimplicial realization `R` and an apartment splitting `T`. Its hypotheses
are precisely the existing Library expressions of the five axioms in the
corrected opening of Kaletha–Prasad Section 4.2:

| Source axiom | Retained Library premise |
| --- | --- |
| 4.1.1, its one-group building clauses | `P.SatisfiesBuildingAxiom R` |
| 4.1.2 | `P.HasBoundedOpenStabilizers` |
| 4.1.4 | `P.SatisfiesAffineApartmentAxiom T` |
| 4.1.6, AS 1 through AS 6 | `P.HasRootReflections`, `P.SatisfiesApartmentAxioms`, and `P.HasCompatibleApartmentFacets` |
| 4.1.9 | `P.HasTitsSystem` |

The cross-group comparisons in 4.1.1 do not enter this one-group consequence.
The three premises in the fourth row are the same decomposition used by
`KPBuildingDatum.SatisfiesAffineRootSystemAxiom`. In particular, the topology
compatibility condition V 7, the affine root systems and AS 5 are retained
inside `SatisfiesApartmentAxioms`, and apartment-map injectivity and facet
compatibility are retained inside AS 6. All the premises concern the same
supplied quotient and apartment. The conclusion is
`Nonempty P.toValuationBuildingData.MetricRealization`.

The provenance is a derived aggregation and local-field specialization of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Section 4.2,
printed pp.168–172 / PDF pp.199–203, read with the authors' corrections of
1 November 2024, PDF pp.28–29. Proposition 4.2.1 constructs the invariant
apartment distance from a compatible system of Weyl-invariant Euclidean
metrics; Proposition 4.2.3 proves that it is a metric; Proposition 4.2.7
proves the midpoint inequality; and Theorem 4.2.10 proves completeness.
The source chooses compatible apartment metrics. This target existentially
forgets their normalization and records only the properties needed by the
supplied-model consumer.

The corrections add Axiom 4.1.6 to the opening hypotheses, explicitly require
invariance in Proposition 4.2.1, and repair the argument that the apartment
distance is independent of the chosen apartment. A proof successor must use
the corrected apartment-comparison argument. The completeness theorem does
not require local finiteness. The continuous-orbit conclusion is an internal
topological deduction from the openness part of 4.1.2: the coset of the
existing norm-one stabilizer at a point is an open neighborhood on which the
orbit map is constant. Local constancy implies continuity for the metric
topology on the same quotient.

The record is an internal interface for these source consequences. Worker 118
proposed the reusable metric and actual-quotient prerequisite boundary;
Worker 1681 formulated this supplied-data source specialization and authored
the Lean and Markdown.

Actual existence of the data and the five axiom witnesses remains a separate
construction obligation. This conditional metric target does not provide
unramified descent, the corrected ten-axiom availability certificate, a
supplied integral-model comparison, a special vertex, a norm-kernel
stabilizer identity, or unique fixation. In particular, its hypotheses are
not added to `IntegralModel.BuildingComparisonStatement`; that unchanged
unconditional theorem still requires actual constructions discharging every
input used along this route.
