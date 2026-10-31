# Induction of actual positive-polyradius affinoid actions

This module constructs a coset family of genuine presented affinoid
algebras, its bounded full-group action, and, for an open subgroup, an
affinoid atlas on the actual balanced quotient of the original spectrum.
The input is a norm-continuous subgroup action on any presented
positive-polyradius affinoid algebra.

The namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction`.
The atlas, bounded maps, quotient identification, and continuity proofs
are constructed from the input algebra action.

## Input and conventions

Let `K : Type u` be a normed field with ultrametric distance,
`G : Type v` a group with a topology, and `H : Subgroup G` with its
inherited topology. The input
`X : PresentedAffinoidAlgebra.NormContinuousAction K H` contains an
actual finite positive-polyradius Tate-algebra quotient `A = X.obj.V`,
a bounded algebra action, and continuity of each forward algebra orbit
`h ↦ (X.actionAut h).hom a` in the original quotient norm.

No ambient rational domain or radius-one presentation is required.
All component algebras are the original `A`, including its nilpotents
and bounded maps. The family index has universe `v`; its total spectrum
has universe `max u v`.

The quotient comparison and joint continuity require
`[IsTopologicalGroup G]` and `hH : IsOpen (H : Set G)`. Constructing
the atlas additionally requires `[CompleteSpace K]`. The algebraic
family action itself does not require openness. There is no finite-index
or nonempty-spectrum hypothesis.

## Representative correction and bounded action

For a left coset `c : G ⧸ H`, let `c.out` be its chosen representative.
The declaration `correction H g c` constructs the subgroup element

`κ(g,c) = (g • c).out⁻¹ * (g * c.out)`.

Membership in `H` follows from equality of the two left cosets.
The implemented lemmas prove

* `g * c.out = (g • c).out * κ(g,c)`;
* `κ(1,c) = 1`;
* `κ(g*h,c) = κ(g,h • c) * κ(h,c)`.

The last identity follows by cancellation of the intermediate chosen
representative. These lemmas are independent of topology.

`family H X` is the actual constant quotient family indexed by `G ⧸ H`.
`pullback H X g c` is the inverse bounded algebra operator
`(X.actionAut κ(g,c)).inv`. Its source and target are both the original
algebra `A`. The inverse is available from the given group action.
The cocycle law and the automorphism multiplication law give

`pullback (g*h) c = (pullback h c).comp (pullback g (h • c))`.

Thus `actionMap H X g` is a morphism in the published
`AffinoidFamily` category with index map `c ↦ g • c` and these
contravariant bounded pullbacks. `actionMap_one` and `actionMap_mul`
prove equality of both the index functions and algebra maps.
`action H X` packages the action in Mathlib's categorical `Action`;
`automorphisms H X` gives its bounded family automorphisms. Inverses
come from the group laws. Algebra maps are never identified merely
because they agree on spectrum points.

## Actual quotient and continuity

`LocalSpectrum H X` is a type synonym for the original
`BanachSpectrum A` with the specified subgroup action
`h • x = x ∘ (X.actionAut h).inv`. Its topology is the original
spectrum topology. The published norm-continuous spectrum construction
proves this subgroup action jointly continuous.
`pullback_spectrum` identifies the point pullback of the constructed
bounded map with `κ(g,c) • x`.

`Spectrum H X` is the published balanced quotient
`TopologicalInduction.Space H (LocalSpectrum H X)`, with its actual
product-quotient topology and full-group action.
For an open `H`, `spectrumHomeomorph H X hH` identifies the family
spectrum with this quotient by

`(c,x) ↦ [c.out,x]`.

This uses the published coset-copies homeomorphism; the target topology
is not replaced. The representative equation and balancing relation
prove `actionMap_realization`:

`g • spectrumHomeomorph p = spectrumHomeomorph (actionMap g).spectrumMap p`.

Consequently, the family point action is conjugate by this homeomorphism
to the jointly continuous quotient action. `continuous_action` proves
joint continuity by composition with the homeomorphism and its inverse.
`continuousSpectrum H X hH` packages the spectrum realization of the
bounded family action as an actual `ContAction TopCat G`.

## Constructed atlas and its action pullbacks

`atlas H X hH` transports the published disjoint affinoid atlas through
`spectrumHomeomorph`. Its index is the subtype of cosets with nonempty
original spectrum. If the spectrum is empty, the total quotient and
atlas are empty; no nonemptiness assumption is introduced.

Each atlas algebra is `A`, and `atlas_chart` identifies its chart as
`x ↦ [c.val.out,x]`. The reused transport construction supplies the
embeddings, locally Hausdorff condition, net of chart domains, bounded
restrictions, their identities and compositions, and the affinoid-domain
factorization property for every presented affinoid test algebra,
including nonstrict test algebras. Distinct component charts are
disjoint. Containment of nonempty component charts forces equality of
their indices, so restrictions are transported bounded identities.

`chartTarget H X hH g c` constructs the translated nonempty chart.
Nonemptiness follows by pulling back an original point along the actual
bounded algebra map. Its identity and multiplication laws are proved.
`image_chart_subset` proves the required chart-image containment.
For every target chart satisfying that containment, `chartTarget_eq`
proves that its index is this translated index.

`chartPullback` supplies the original bounded operator `pullback g c.val`
for every such admissible source/target chart pair.
`chartPullback_chart` proves its spectrum realization is the full-group
point action. `chartPullback_naturality` proves compatibility with
restrictions in both the source and target atlas as an equality of
bounded algebra maps: chart containment first identifies the respective
indices, and the two restrictions then reduce to identities.
`chartPullback_one` is the bounded identity. `chartPullback_mul` proves
the contravariant composition law on every compatible triple of charts
by identifying the intermediate index and applying `pullback_mul`.

## Provenance and remaining scope

The original motivation is Berkovich, unfinished *Etale equivariant
sheaves on p-adic analytic spaces* (1995–1996), Construction 1.1.2,
printed/PDF page 2. The registered folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
with folder digest
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

That construction uses copies indexed by `G/H` and acts between copies
by the subgroup element determined by `g*g_i = g_j*h`. The implemented
correction is precisely that element. This module internally derives
the bounded pullbacks, group laws, actual quotient identification and
atlas-action compatibility in the genuine affinoid-input case. It reuses
the published `NormContinuousAction`, `DisjointAffinoidMorphisms`,
`DisjointAffinoidTransport` and `InducedCharts` constructions by Lean
name. Their original algebras and topologies are preserved.

The source uses continuity into the analytic automorphism group.
This module proves joint continuity on the spectrum from norm-continuous
algebra orbits; it does not prove comparison with that analytic
automorphism topology. It does not construct induction on arbitrary
overlapping analytic atlases, an analytic induction adjunction, etale
or quasi-etale sites, or the Harris tower specialization. Those remain
separate construction obligations.
