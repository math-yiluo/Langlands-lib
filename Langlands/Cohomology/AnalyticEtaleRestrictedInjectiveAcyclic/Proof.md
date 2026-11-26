# Acyclicity of restricted injective analytic étale G-sheaves: proof

Module `Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.Proof`, namespace
`Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic`.

The theorem `analyticEtaleRestrictedInjectiveAcyclic` proves
`AnalyticEtaleRestrictedInjectiveAcyclicStatement L X h G ρ R` (module
`Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.Statement`), with no
hypotheses beyond the parameters and instances of the statement.

## What is proved

The parameters are those of the statement: a complete ultrametric normed field `K`, a
normed extension field `L`, an analytic space `X`, point axioms `h` for all its
`L`-valued points, a group `G` with `[TopologicalSpace G]` and `[IsTopologicalGroup G]`
acting through `ρ : G →* Aut X`, with `[Small.{max u (v + 1) uL} G]` and admissible
refinements of the distinguished lift system for the twisted étale topology, and a
commutative ring `R` in universe `max u (v + 1) uL`. The universes `u`, `v`, `uL` and
`z` are independent. The theorem proves the conjunction of two assertions.

1. If `|X|` is Hausdorff, `pointProjection L X` is surjective and the action is
   continuous, then for every injective object `I` of `EtaleGSheaf ρ` and every
   `q : ℕ`, `(etaleCompactCohomology L h R (q + 1)).obj ((etaleGSheafRestriction ρ R).obj I)`
   is zero.
2. If moreover `|X|` is compact, then
   `(etaleCohomology X R (q + 1)).obj ((etaleGSheafRestriction ρ R).obj I)` is zero.

Injectivity of `I` is injectivity in the category of étale `G`-sheaves. The proof does
not show, and does not use, that the restriction `etaleGSheafRestriction` (Berkovich's
`b^*`) preserves injective objects.

## The implemented proof

The proof is the application of the reduction
`analyticEtaleRestrictedInjectiveAcyclic_of_godement` (module
`Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.GodementReduction`) to two
proved results:

- `analyticEtalePointFibersJointlyFaithful` (module
  `Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.PointFibersJointlyFaithful`),
  which proves `AnalyticEtalePointFibersJointlyFaithfulStatement L X h R`: on Hausdorff
  `|X|` with surjective `pointProjection L X`, the sheaf-fibre functors
  `(etalePoints L h x).sheafFiber` of the actual `L`-valued points jointly detect
  morphisms of étale module sheaves;
- `analyticEtaleGodementCompactAcyclic` (module
  `Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.GodementCompactAcyclicProof`),
  which proves `AnalyticEtaleGodementCompactAcyclicStatement L X h R G ρ`: under the
  hypotheses of assertion 1, for every étale `G`-sheaf `F` (injective or not),
  `etaleCompactCohomology L h R (q + 1)` vanishes on the restriction of the degree-zero
  equivariant Godement term `(etaleGodementZeroFunctor L ρ h R).obj F`.

Inside the reduction the argument runs as follows.

**Compact-support component.** Fix `I` injective and `q`. Joint faithfulness of the
point fibres makes the Godement coaugmentation
`(etaleGodementCoaugmentation L ρ h R).app I` a monomorphism
(`mono_etaleGodementCoaugmentation_of_jointlyFaithful`, module
`Langlands.Sheaf.Equivariant.AnalyticEtaleGodement`). The Godement functor is built on
the family `etaleGodementPoints L h`, the actual point family `etalePoints L h` reindexed
by `ULift` to the universe of the coefficients; joint faithfulness passes to this
reindexed family by forgetting the lift. Since `I` is injective in `EtaleGSheaf ρ`, the
identity of `I` factors through this monomorphism, so `I` is a retract of its Godement
term (`etaleGodementRetractOfInjective`). The retraction is mapped by the composite
functor `etaleGSheafRestriction ρ R ⋙ etaleCompactCohomology L h R (q + 1)`; the image of
`I` is then a retract, in particular a subobject, of the image of the Godement term,
which is zero by `analyticEtaleGodementCompactAcyclic`. This is
`isZero_etaleCompactCohomology_restriction_of_godementZero`. The retraction lives in the
equivariant category and is only afterwards restricted, which is why no preservation of
injectives by restriction is needed.

**Ordinary component on compact spaces.** The theorem
`analyticEtaleRestrictedInjectiveAcyclic_of_compact` derives assertion 2 from
assertion 1 using the supplied point axioms `h`, although the ordinary statement itself
does not bind `h`. It applies `isZero_etaleCompactCohomology_iff_of_compactSpace`
(module `Langlands.Sheaf.Equivariant.AnalyticEtaleCompactGlobal`) in degree `q + 1` to
the restricted sheaf `(etaleGSheafRestriction ρ R).obj I`.

## Support and derived-functor identifications used

- **Supports.** `etaleCompactSections L h R` is the functor of sections over
  `etaleSelf X` whose support, a set of `L`-valued points of `X`, lies in a compact
  subset for `pointTopology L X`, the topology induced from `|X|` by
  `pointProjection L X`. When `pointProjection L X` is surjective,
  `exists_isCompact_superset_iff_of_surjective` identifies such bounds with compact
  subsets of `|X|` containing the image of the support. On compact `|X|` the whole space
  bounds every support (`isCompactlySupported_etalePoints_of_compactSpace`), so the
  inclusion `etaleCompactSectionsInclusion` of compactly supported sections into all
  sections `etaleSections X R` is an isomorphism (`etaleCompactSectionsIsoOfCompactSpace`).
- **Derived functors.** `etaleCompactCohomology L h R q` and `etaleCohomology X R q` are
  the right derived functors, computed by injective resolutions of étale module sheaves,
  of `etaleCompactSections L h R` and of `etaleSections X R`. Deriving the natural
  isomorphism of sections in each degree gives
  `etaleCompactCohomologyIsoOfCompactSpace`, from which
  `isZero_etaleCompactCohomology_iff_of_compactSpace` follows. The vanishing in
  assertion 1 is that of these actual derived functors of compactly supported sections
  on the restricted sheaf, not a definition of acyclicity by softness.
- **Godement compact acyclicity.** The proof of `analyticEtaleGodementCompactAcyclic`,
  described in `GodementCompactAcyclicProof.md`, compares étale and ordinary compact
  cohomology through the ordinary-topology restriction of étale module sheaves. It uses
  the vanishing of the positive ordinary higher direct images of the restricted smooth
  point products, from their coinduced fixed sections over finite Galois data, and the
  c-softness of their ordinary restriction together with the acyclicity of c-soft
  sheaves for compact supports (`Langlands.Cohomology.cSoftAcyclicity`).

## Independence

The constants reached by the proof term, through types and values, were scanned
transitively from `analyticEtaleRestrictedInjectiveAcyclic`. The scan reached none of
`AnalyticEtaleCompactComparisonStatement`, `AnalyticEtaleCompactDerivedComparisonStatement`,
`AnalyticEtaleGlobalComparisonStatement` and `analyticEtaleGlobalComparison`, no
constant of the namespaces `Langlands.Cohomology.AnalyticEtaleCompactComparison` and
`Langlands.Cohomology.AnalyticEtaleGlobalComparison`, and no constant of the modules
under those names, of `Langlands.Sheaf.Equivariant.AnalyticEtaleCompactSmoothness` or of
`Langlands.Cohomology.DivisibleSystem`. Since a theorem assuming a comparison has the
comparison statement in its type, no such theorem is used. The proof has no
hypotheses, so no unproved Library proposition is a premise. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Source

The route is Berkovich's: Vladimir G. Berkovich, *Étale equivariant sheaves on p-adic
analytic spaces* (manuscript, 1995–1996), §1.5. Proposition 1.5.1, printed pp. 10–11,
shows that the terms of the equivariant Godement resolution restrict to soft étale
sheaves, and the proof of Corollary 1.5.2, printed pp. 11–12, uses the resulting
acyclicity of `b^*` of injective equivariant sheaves for the comparisons of cohomology.
The statement proved here is derived from that argument and is not a verbatim statement
of the source. The Lean proof replaces softness of the Godement terms by the vanishing
of their compactly supported étale cohomology, proved as described above, and obtains
the injective case through the Godement retraction.
