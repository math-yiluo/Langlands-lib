# Renard I.5.2: ideal projectivity and enough projectives

This proof implements all four assertions of the published
`NonUnitalModuleEnoughProjectivesStatements` interface, culminating in
`NonUnitalModuleProjectivityProof.projectivityAssertions`. It imports the
public target directly and does not modify its statement or dependencies.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, I.5.2, printed pp.26–27 / PDF pp.32–33,
registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1210 checked both original pages and the registered supplementary
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.1–3. The nearby corrections concern admissibility and the
dual-injectivity lemma; they do not alter this enough-projectives argument.
The original source's ideal and sum argument uses only idempotented ring and
additive module laws, so the ring-general hypotheses preserve its complex case.

For the original Ae object, an epimorphism of nondegenerate modules is
surjective on its original underlying function by the published concrete
criterion. The published fixed-part surjectivity proof lifts a fixed vector by
applying e to any original preimage. Apply this to the value at e of the given
map from Ae. The inverse of the actual additive Hom evaluation equivalence then
gives an original intertwiner into the epi's domain. Equality after composition
is checked at e via the same injective equivalence. This proves categorical
projectivity without an assumed exactness property.

For a specified coproduct cofan, lift the composite of every injection with the
given map through the epimorphism, use the cofan's full colimit universal
property to assemble these lifts, and compare maps on every injection.
The index universe is independent; the proof assumes only the indicated
coproduct and does not claim arbitrary-size coproduct existence.

All source-Hom conclusions use the named
`NondegenerateModuleCat.abelian.{uA, max uA uM} A hA` structure. The published
`Langlands.Renard.homProjectiveComparison` identifies the categorical lifting
condition with `Langlands.Renard.HomProjective`, which means sequence exactness
of the actual integer-module-valued covariant Hom functor
`Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt`. Its maps are actual
postcomposition. The comparison uses the Hom functor's left exactness and
identifies preservation of epimorphisms with surjectivity of postcomposition.
Thus `idealProjectivity` converts the ideal lifting proof to the specified
source predicate. `directSumProjectivity` first converts each summand's source
predicate to categorical projectivity, applies `cofan_projective`, and converts
back. `surjectiveProjectiveCover` applies the same comparison to its explicitly
constructed domain. The book instead presents the ideal step through exactness
of the fixed-part functor; the implemented lifting route proves the same public
predicate without adding an exactness premise.

For each original vector m of M, `chosenIdempotent` chooses an actual e_m
fixing m. `presentationFamily` consists of the original ideal objects A e_m.
`presentationObject` is their actual finitely supported direct sum, using
`NonUnitalModuleDirectSum`'s coordinate actions and complete cofan universal
property. `presentationMap` assembles the original orbit intertwiners
x ↦ x m from these ideals. The singleton vector e_m in the summand indexed
by m maps to e_m m = m; this proves surjectivity on the entire original
underlying additive map. The cofan lifting result makes the domain projective,
and the published concrete epi criterion makes the map an epimorphism.
`presentation` therefore is a genuine Mathlib `ProjectivePresentation M`.

`enoughProjectives` packages this presentation for every M in
`EnoughProjectives`. `surjectiveProjectiveCover` records its domain, original
map, source-Hom projectivity, epimorphism and underlying surjectivity.
`projectivityAssertions` combines these with the ideal and existing-direct-sum
assertions. No minimality property of the presentation is asserted.

The category's carrier universe is `max uA uM`. The family is indexed by the
original carrier of M in that same universe, and its actual Ae summands and
finite-support sum remain there. No resizing or smallness axiom is used.
Ring and chosen carrier universes remain independent, and the existing-cofan
assertion also retains an independent index universe.

Complete unapplied interface examples check the universally quantified aggregate
at independent `uA,uM,uI`, both unequal ring/carrier-universe orders and an index
universe larger than the carrier universe for the existing-cofan assertion.
Enough injectives, free modules and I.6's further structural assertions remain
separate obligations. Local compilation alone does not establish independent
acceptance or publication.

Worker 6 authored the reused shared proof draft revision 1. Worker 1210 checked
its source correspondence, original maps, named exact-Hom comparison and
unchanged public interfaces, and expanded this proof explanation.
