# Continuous equivariant diagrams of weighted rational charts

This internal construction assembles the published weighted rational stabilizer,
section continuity and locus continuity constructions over one common open
subgroup. The intended entry point is `normInvariantSpectrumLocusIso`. The
underlying spaces, algebras and maps are the existing actual rational quotients,
bounded algebra restrictions, multiplicative seminorm spectra and inequality
loci. The construction is proved in the paired Lean file.

Let `K` be an ultrametric normed field, `A` an actual presented weighted affinoid
algebra and `G` a topological group, with independent field and group universes.
The input is a homomorphism `ρ : G →* Aut A` of actual bounded algebra
automorphisms and continuity of each forward algebra orbit in the quotient norm.
For an open subgroup `H`, the full category `NormInvariantChart ρ hρ H` consists
of the existing weighted rational charts `d` for which `H` is contained in the
derived full setwise stabilizer of `d.locus`. It retains every actual bounded
restriction over `A` between its objects. The property concerns the locus, not
the displayed coefficient representatives. `finiteNormInvariantChart` bundles
every chart of a finite family over the already derived simultaneous open
stabilizer inside any prescribed open subgroup.

The continuous inclusion `normInvariantStabilizerInclusion` retains the same
ambient group element and the inherited subgroup topologies. Restricting the
published continuous locus action along this inclusion gives
`normInvariantLocusAction`. Actual bounded restrictions induce the original
continuous subspace inclusions. Their equivariance holds because the source
and target operators are the same ambient point operator. Thus
`normInvariantLocusFunctor` takes values in Mathlib's continuous action category.
Forgetting the actions gives exactly the existing `locusFunctor` restricted to
the full invariant category.

Assume now that `K` is complete. `normInvariantSectionAction` restricts the
published `normContinuousSectionAction`; it retains the entire weighted
rational quotient with its original quotient norm. Its `actionAut` is proved
equal to the original bounded section action composed with the continuous
stabilizer inclusion, including the inverse bounded maps. The base-map equation
is inherited from `normSectionAction_baseMap`.
`normInvariantSectionAction_restriction` reuses the published equality
`normSectionAction_restriction` for the same ambient element preserving both
loci. Consequently every retained bounded restriction is equivariant, and
`normInvariantBoundedPresheaf` is a presheaf with values in norm-continuous
actions on actual presented affinoid algebras. Its forget equation recovers
exactly the original bounded rational section presheaf. The structural bounded
base maps form the equivariant natural transformation
`normInvariantBaseMapNat`; the base action is the original action restricted to
`H`, and naturality is the original equation over the base.

`normInvariantSpectrumFunctor` reverses the algebra direction and applies the
published `NormContinuousAction.spectrumFunctor`. Thus joint continuity of
every spectrum action follows from the constructed quotient-norm continuous
section orbits. The point action is inverse pullback by the original local
bounded automorphism, and every arrow is pullback along the original bounded
restriction. The underlying topological functor is exactly the existing
`toTopologicalSpace` on the invariant full category.

Finally, `normInvariantSpectrumLocusIso` uses each existing
`d.locusHomeomorph`. Its equivariance is the published
`normSectionAction_locusHomeomorph`, after identifying the restricted section
action. Its naturality is the existing
`Restriction.locusHomeomorph_naturality`. Mathlib's full-subcategory and action
isomorphism constructors give the inverse equivariant continuous maps. After
forgetting the actions, this natural isomorphism is exactly the restriction of
the published `spectrumLocusIso`.

The locus construction needs no coefficient completeness. Completeness is used
for the section action and its norm continuity, and hence for the assembled
spectrum construction. No reducedness, nonzero algebra, nonempty spectrum or
locus, positive arity, nontrivial valuation or value-group radius restriction
is added. Empty finite families are allowed. The subgroup topology is never
replaced by a discrete topology.

## Provenance and source conventions

Worker 56 assembles the published `RationalNormStabilizer`,
`RationalNormSectionContinuity`, `RationalNormContinuousLocus`,
`RationalChartCategory` and `NormContinuousAction` APIs. The full invariant
category and continuous stabilizer inclusion follow the internal pattern of
`DomainInvariantActions` and `DomainContinuousLocus` by Worker 56, with the
Worker 36 invariant-action packaging pattern adapted in the former. Worker 36
is credited for that reused pattern. Those older
constructions assume continuity into a domain-spectral automorphism topology;
this construction uses the separately proved consequences of norm-continuous
base-algebra orbits and the rational spectrum homeomorphisms. It does not
assume continuity into the full analytic automorphism topology.

The original geometric conventions are in Vladimir G. Berkovich,
*Non-archimedean analytic spaces* (Trieste lectures, 2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA-256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`:
printed/PDF p.4, Example 1.2.2(v), Definitions 1.2.3 and 1.2.5; pp.7–8,
Definition 2.1.2 and Definition 2.1.11; pp.9–10, Definition 2.2.1,
Exercise 2.2.2(ii), Fact 2.2.3 and Definition 2.2.7. These passages supply
positive real radii, bounded seminorm spectra, admissible quotient presentations,
bounded morphisms, represented domains and rational inequalities. The source
uses complete nonarchimedean fields; the locus-only incomplete-field extension
above is internal. Explicit unit generation is the stored rational-chart
hypothesis. No converse from absence of common zeros to unit generation is
used.

The motivation for continuous group actions and equivariant morphisms is
Berkovich's unfinished 1995–1996 manuscript *Étale equivariant sheaves on
p-adic analytic spaces*, registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
PDF SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`,
section 1.1, printed/PDF pp.1–2. The fixed-subgroup rational diagrams and their
Lean packaging here are internal derivations, not a claimed theorem quoted
from that manuscript.

This construction supplies local continuous equivariant rational diagrams.
General analytic atlases, arbitrary compact or distinguished domains, the full
analytic automorphism topology, sheaf descent, analytic étale and quasi-étale
sites, Harris tower morphisms and cohomological comparison remain separate
obligations.
