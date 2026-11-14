# Complete NPC metric input for actual unramified buildings

`MaximalUnramified.CompleteNPCMetricStatement.{u}` is an **unproved
proposition**, at arbitrary universe `u`. It asks for a complete nonpositively
curved metric on the original reduced quotient of every supplied
`MaximalUnramified.BuildingData F G`, with its existing rational-point action
isometric. This pair does not construct such a metric.

For any integer-valued building datum `B`, the structure
`IntegerValuationBuildingData.CompleteNPCMetric` packages a `MetricSpace` on
`B.ReducedBuilding`, completeness of that metric, nonpositive curvature in the
sense of `Langlands.Geometry.Metric.KP.IsNonpositivelyCurved` (KP Definition
1.1.8), and isometry of the original `rationalPoints G` action. The metric
determines the topology used for completeness. No normalization, comparison
topology, or continuity of orbit maps is prescribed.

The existence statement specializes this structure to a nonarchimedean local
field `F`, its actual maximal unramified field `K = inertiaFixedField F`, an
arbitrary affine group scheme `G` over `K`, and supplied building data `B`.
Connected reductivity and the maximal split torus are already fields of `B`.
The statement neither asserts that such building data exist nor treats `K` as
a local field. It assumes no local compactness or local finiteness.

Unlike `Langlands.Geometry.Building.UnramifiedBuildingMetricStatement`, this
statement permits an arbitrary group over `K` and arbitrary supplied building
data, without descent from an `F`-group or Galois stability. It requests no
coefficient-automorphism isometries. The two existence propositions therefore
have different scopes; the narrower statement alone does not supply this input.
The generic structure above makes no metric-existence assertion for arbitrary
integer-valued fields.

## Derived source provenance

The motivation is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
with the corrections and additions of 1 November 2024:

- Propositions 4.2.1 and 4.2.3, printed pp.168–169 / PDF pp.199–200:
  a compatible invariant Euclidean distance on apartments extends to the
  building and the group action is isometric.
- Proposition 4.2.7 and Theorem 4.2.10, printed pp.170–172 / PDF pp.201–203:
  nonpositive curvature and completeness, including buildings that are not
  locally finite.
- Proposition 7.6.3 and Remark 7.6.5, printed pp.264–266 / PDF pp.295–297:
  the root-valuation quotient and its building axioms.
- Corrections, PDF pp.25–30 and p.33: the additional Axiom 4.1.6 at the opening
  of Section 4.2, the invariant apartment metric and corrected comparison
  action, and the extra AS 5 hypothesis in Chapter 7. The general
  perfect-residue-field route referred to there is Theorem 9.4.35.

This is a derived metric-existence obligation for the Library's exact supplied
quotient, rather than a verbatim source assertion. Establishing the hypotheses
of the corrected building and metric results for every such `B`, constructing
the metric, and proving its properties remain obligations of a proof of
`CompleteNPCMetricStatement`. Neither the supplied structure nor the citations
discharge those obligations.

Together with common apartments and algebraic boundedness of one-stabilizers,
this input is intended to provide fixed points for algebraically bounded
subgroups through the existing complete NPC bounded-action theorem. That
application and vertex-stabilizer maximality are not conclusions of this pair.
