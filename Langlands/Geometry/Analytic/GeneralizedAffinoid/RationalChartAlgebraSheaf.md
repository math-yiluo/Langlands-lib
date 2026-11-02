# The actual algebra sheaf on the finite rational chart site

For a complete ultrametric normed field `K : Type u` and an actual
`PresentedAffinoidAlgebra K` named `A`, `RationalChart.algebraSheaf K A`
is a Mathlib `Sheaf (finiteRationalTopology K A) (CommAlgCat K)`.
Its values are the existing weighted closed rational quotient algebras.
Its restriction maps are the underlying algebra maps of the existing
bounded restrictions. The constructor uses the published, unconditional
`rationalPresheafIsSheaf` theorem, so no descent or sheaf premise is supplied.
The field, base presentation, and rational radii retain their existing
generality, including trivial valuations, nilpotents, zero quotients, and
empty covering families.

This is the algebra sheaf on the **finite rational chart site**. The module
does not extend that topology to the full analytic G-topology, construct an
analytic atlas or a locally ringed topological space, prove a Banach-valued
sheaf assertion, or assert higher cohomological acyclicity.

## Bounded coefficient morphisms

For an arbitrary `BoundedAlgHom K A B` named `φ`, `algebraSheafMap φ`
constructs a sheaf morphism

```text
algebraSheaf K A → coefficientSheafPushforward φ (CommAlgCat K)
                    (algebraSheaf K B).
```

The direct image is the existing continuous direct image on the finite
rational sites. At a chart `d` its value is the actual algebra of the
chosen coefficient pullback `pullback φ d`. The morphism's component is the
underlying algebra map of the bounded quotient map `pullbackMap φ d`.
Naturality is the already proved quotient-transport/restriction square
`pullbackRestriction_comp_pullbackMap`. In particular, the component sends
`d.baseMap a` to `(pullback φ d).baseMap (φ a)`.

The equality `algebraSheafMap_id` uses the actual identity-pullback chart
isomorphism. Its inverse restriction composed with `pullbackMap id d`
is the identity, by `pullbackIdIso_hom_restriction` and the chart
isomorphism's inverse law.

The equality `algebraSheafMap_comp` states that applying the two coefficient
morphisms successively and then the existing direct-image comparison gives
the morphism for `ψ.comp φ`. At each chart this is exactly the bounded-map
equation `pullbackCompIso_hom_transport`. Both equalities are between
actual sheaf morphisms, with the direct-image comparisons present in
their types; the chosen quotient presentations are not identified by
definitional equality.

## Whole-chart sections

`wholeSectionIso K A` is an isomorphism in `CommAlgCat K` from `A`
to the value of the constructed sheaf on `whole K A`. It is the underlying
algebra equivalence of the previously constructed `wholeEquiv K A`.
The forward map is the actual whole-chart structural map, and the
inverse is the actual bounded `wholeRetraction K A`.

`wholeSectionIso_restrict` says that restricting this section to any
chosen chart is the original `d.baseMap`. Its proof evaluates the
constructed whole-chart restriction and uses
`wholeRetraction_baseMap`.

`wholeSectionIso_naturality` states that the coefficient sheaf morphism
recovers the original `φ` on whole-chart sections. Its formula includes
the actual inverse restriction of `pullbackWholeIso φ` to compare the
pulled-back whole chart with `whole K B`. The proof uses
`pullbackMap_baseMap` and that comparison's equation over `B`.
Thus the sheaf construction retains both the actual base algebra and its
bounded coefficient maps.

## Provenance

This is an internal categorical construction by Worker 36 from the
published rational quotient, bounded map, finite rational topology,
sheafness, and coherence declarations imported in the Lean module.
It does not reprove the analytic descent theorem. In particular,
the sheaf proof is `rationalPresheafIsSheaf` from `RationalSheafProof`;
the bounded coefficient maps are from `RationalChartBaseChange`;
continuity and direct image are from `RationalChartCoverBaseChange`;
the sheaf comparisons are from `RationalChartSheafCoherence`; and the
whole-chart equivalence is from `RationalChartTerminal`.

The geometric source context is Berkovich, *Non-archimedean analytic
spaces*, Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`:
Definition 2.2.1 and Exercise 2.2.2(ii)–(iii), printed/PDF page 9,
give the positive-radius rational quotients and intersections;
Fact 2.2.6(i), page 10, gives the stronger finite-cover exactness context;
Exercise 3.2.5(ii)–(iii), page 15, identifies affinoid function algebras
and states the structural sheaf on the full G-topology.
The present module only packages the already proved finite rational-site
algebra sheaf and its actual coefficient morphisms. It does not assert
those stronger source conclusions.
