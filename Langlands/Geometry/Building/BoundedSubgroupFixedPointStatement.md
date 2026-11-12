# Fixed points of bounded subgroups in the actual KP quotient

`Langlands.Geometry.Building.BoundedSubgroupFixedPointStatement` is a
Prop-valued `def` at every universe `u`. It states, for supplied data
satisfying the five axioms of the corrected opening of Kaletha–Prasad
Section 4.2, the local-field form of the conclusion of KP Corollary 4.2.14:
an algebraically bounded subgroup of `G(F)` fixes a point of the building,
and fixes a point of every nonempty closed convex subset that it preserves.
The module supplies no proof.

## Statement

The proposition quantifies over:

- every nonarchimedean local field `F`, of mixed or equal characteristic
  (`[Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]`);
- every group scheme `G` over `Spec F` with `hG : IsConnectedReductive G`
  (the instances `IsAffineHom G.X.hom` and `IsAffine G.X.left` are derived
  from `hG`);
- supplied `P : ParahoricBuildingData G`, a polysimplicial realization `R` and
  an apartment splitting `T` of `P.toValuationBuildingData`.

Its premises are the existing Library expressions of the five axioms, in the
same order and form as in `MetricRealizationStatement`:

| Source axiom | Premise |
| --- | --- |
| 4.1.1, one-group building clauses | `P.SatisfiesBuildingAxiom R` |
| 4.1.2 | `P.HasBoundedOpenStabilizers` |
| 4.1.4 | `P.SatisfiesAffineApartmentAxiom T` |
| 4.1.6, AS 1–AS 6 | `P.HasRootReflections`, `P.SatisfiesApartmentAxioms`, `P.HasCompatibleApartmentFacets` |
| 4.1.9 | `P.HasTitsSystem` |

Then, for every subgroup `H` of `rationalPoints G` with
`IsAlgebraicallyBounded F G.X (H : Set (rationalPoints G))`, the conclusion
is the conjunction of:

1. `∃ x : P.toValuationBuildingData.ReducedBuilding, ∀ h ∈ H, h • x = x`:
   one point of the existing quotient is fixed by every element of `H`;
2. for every `M : P.toValuationBuildingData.MetricRealization`, with the
   metric `M.metric` installed on the quotient, and every set `Y` of
   quotient points that is closed for that metric, satisfies
   `Langlands.Geometry.Metric.KP.IsGeodesicallyConvex Y` (which includes
   nonemptiness) and satisfies `∀ h ∈ H, ∀ y ∈ Y, h • y ∈ Y`, there is
   `x ∈ Y` with `h • x = x` for all `h ∈ H`.

The action is the existing action of `rationalPoints G` on the existing
quotient `ReducedBuilding`. In both clauses the point is chosen before the
quantifier over `h`.

## Source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

- Corollary 4.2.14, printed p.173 / PDF p.204. KP assume the hypotheses of
  Section 4.2 and a bounded subgroup `H` of `G(k)`. They conclude that `H`
  fixes a point of `B(G)`, and that it fixes a point of any nonempty closed
  convex subset `Y` of `B(G)` that it preserves. `Y` need not be bounded.
- Definition 2.2.1, printed pp.70–71 / PDF pp.101–102: boundedness of a
  subset of `G(k)`. The Library predicate `IsAlgebraicallyBounded`
  (module `Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness`)
  formalizes it, so `H` is bounded in exactly KP's sense.

The authors' corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp.28–29, add Axiom 4.1.6 to the standing hypotheses of Section 4.2.
They make the metric of Proposition 4.2.1 `G`-invariant. The five premises
above include 4.1.6. Convexity is the corrected notion (convex sets are
nonempty, corrections PDF pp.1–2), which is the Library's
`IsGeodesicallyConvex`.

This author could not open the source PDF in the session that produced
this unit. The source content above is taken from the published Corollary
4.2.14 row of the KP source ledger (`notes/bruhat-tits/kp-source-ledger.md`),
which records it with the same locators. The reviewer should compare the
statement with the original passage.

## Derived scope and provenance

This is a derived specialization of the source corollary, not a literal
transcription. It differs from the source in three ways.

- **Field.** KP work over a discretely valued field with Henselian valuation
  ring and perfect residue field. The statement covers nonarchimedean local
  fields of either characteristic, which are of that kind.
- **Building and axioms.** The building is the existing quotient of supplied
  `ParahoricBuildingData`. The source's Section 4.2 hypotheses are the five
  Library axiom predicates displayed above, exactly those of the published
  `MetricRealizationStatement`. No existence of the data or of the axiom
  witnesses is asserted. Existence is the separate target
  `RootValuationBuildingConstructionStatement`.
- **Metric.** The first clause needs no metric. In the second clause
  "closed" and "convex" refer to the metric of an arbitrary
  `MetricRealization` of the same quotient: a complete NPC metric with
  isometric action and continuous orbit maps for `rationalPointTopology F G.X`.
  The source uses the specific metric of Proposition 4.2.1. That metric
  gives such a realization by the published `metricRealization`, so the
  universally quantified clause includes the source's case. Nothing is
  assumed about which realization is chosen.

The intended proof combines published results: the metric realization
(`MetricRealizationStatement`), compactness of the closure of an
algebraically bounded set in the canonical topology, continuity of orbit
maps, the bounded-set fixed-point theorem (KP Theorem 1.1.15(2)) and the
equivariant nearest-point projection (KP Proposition 1.1.20). According to
the ledger row, the source proof goes through Proposition 4.2.13 (algebraic
boundedness and bounded orbits). This statement neither states nor needs
that proposition.

The statement does not identify the fixed point with a vertex, facet or
parahoric, and does not assert that maximal bounded subgroups are point
stabilizers. Those are separate consumers.
