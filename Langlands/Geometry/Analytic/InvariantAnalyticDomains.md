# Open and invariant analytic domains and restricted group actions

Author: Worker 21.

This module adds three things to the Library's analytic domains
(`AnalyticDomainSpaces`) of the analytic spaces of `LocalizedCategory`:

1. every open subset of an analytic space is an analytic domain;
2. a morphism of analytic spaces whose image lies in a domain `D` factors
   uniquely through the canonical morphism `ν : D → X`, and so morphisms
   restrict to domains;
3. if a monoid `G` acts on `X` and every element of `G` maps a domain `D`
   into itself, then `G` acts on `D` and `ν` is equivariant. For a
   `G`-space `X`, `D` is then a `G`-space once the restricted action is known
   to be continuous. That continuity is stated separately in
   `InvariantDomainContinuityStatement`.

Item 3 is the construction behind the actions of open subgroups on invariant
domains in Berkovich's manuscript, and behind Harris's actions of the
stabilizers `S(ê)` on the domains `U(ê)`. Everything in this module is
proved.

## Original sources

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The paragraph after Definition 1.3.1, printed p.23 / PDF p.20, says:

> Furthermore, the family of Φ-affinoid domains that are contained in a
> Φ-analytic domain Y ⊂ X defines a Φ_k-affinoid atlas on Y, and there is a
> canonical morphism of Φ_k-analytic spaces ν : Y → X. For any morphism
> φ : Z → X with φ(Z) ⊂ Y there exists a unique morphism ψ : Z → Y with
> φ = ν∘ψ. … If the class Φ_K is dense, then all open subsets of X are
> Φ-analytic domains.

Density is defined on printed p.16 / PDF p.13:

> The class Φ_K is said to be dense if each point of each X ∈ Φ_K has a
> fundamental system of affinoid neighborhoods V ∈ Φ_K.

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.4, printed p.7 (PDF page = printed page). For a distinguished étale
morphism `𝒰 ↪ U → X` with `U` compact and quasi-étale over `X`:

> For such a morphism the action of G on X extends in a canonical way to a
> continuous action of an open subgroup G_U ⊂ G. Since U∖𝒰 is a compact
> analytic domain in U, then 𝒰 is invariant under the action of an open
> subgroup G_𝒰 ⊂ G_U.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`,
§2, printed p.303 (PDF page = printed page − 298):

> Recall that the action of G_J on Ω lifts to an action on ℳ_N, and U(ê) is
> stabilized by a compact open subgroup S(ê) ⊂ G_J.

In both places the group acting on the domain is the stabilizer, and its
action is the restriction of the ambient action. The construction below
produces exactly that restricted action.

## Open subsets are analytic domains

`IndexedAffinoidAtlas.HasAllLocalDomains.isOriginalChartDomain_of_isOpen`:
in an atlas that contains every affinoid domain of each of its charts
(`HasAllLocalDomains`), every open subset `U` satisfies the Library's domain
condition `IsOriginalChartDomain`. Proof:

- The sets `range(chart i) ∩ U` locally refine `U`. At `x ∈ U` the atlas net
  gives finitely many charts containing `x` whose union is a neighbourhood
  of `x`. Their intersections with `U` contain `x` and lie in `U`, and their
  union is a neighbourhood of `x` within `U`.
- Each `range(chart i) ∩ U` is locally refined by charts. Let
  `x = chart i y ∈ U`. Since `chart i` is continuous, `chart i ⁻¹' U` is an
  open neighbourhood of `y` in the spectrum. The Library theorem
  `PresentedAffinoidAlgebra.RationalChart.exists_rational_neighborhood` gives
  a rational chart `d` whose locus is a neighbourhood of `y` contained in
  `chart i ⁻¹' U`. The affinoid domain `d.toDomain` of chart `i` is a local
  domain, so `HasAllLocalDomains.exists_chart` gives a chart `k` with range
  `chart i '' d.locus`. This range lies in `range(chart i) ∩ U`, contains
  `x`, and is a neighbourhood of `x` within `range(chart i)`, because
  `chart i` is an embedding (`IsInducing.image_mem_nhdsWithin`). It is
  therefore also a neighbourhood within `range(chart i) ∩ U`.
- `AtlasTopology.LocallyRefines.trans` composes the two refinements, and
  `AtlasTopology.isQuasinet_restrictedFamily_iff` turns the result into the
  domain condition.

Provenance. The Library's charts are presented affinoid algebras with
arbitrary positive real polyradii, and
`exists_rational_neighborhood` says that the loci of rational charts with
arbitrary positive real thresholds form a neighbourhood basis of each
spectrum. This is Berkovich's density of the class of all affinoid spaces.
The lemma is the Library form of the sentence "If the class Φ_K is dense,
then all open subsets of X are Φ-analytic domains". No Hausdorff hypothesis
is needed.

`SaturatedAtlasPresentation.openDomain S U hU` is the open subset `U` as an
analytic domain of the saturated presentation `S`; `openDomain_carrier`
records its subset.

## Factorization through a domain

Worker 36's module `SaturatedDomainCorestriction` proves the factorization
property in the source-quotient category `SourceCategory`
(`SourceCategory.domainInclusion_mono`, `SourceCategory.exists_domainFactor`).
Worker 36's module `SaturatedSourceCategory` proves that its comparison
functor `SourceCategory.comparisonFunctor` to `LocalizedCategory` is full,
faithful and surjective on objects. The presentation
`S.originalDomain D` used there and the presentation `S.domain D` of
`AnalyticDomainSpaces` have the same atlas (both are the Library's
`originalDomainPresentation`). They differ only in the proof of saturation,
so their inclusions are the same strong map.

- `comparisonFunctor_map_domainInclusion`: the comparison functor sends
  Worker 36's inclusion to `S.localizedDomainInclusion D`. Both functors are
  defined through `sourceHomEquiv`, so this is `Equiv.apply_symm_apply`.
- `localizedDomainInclusion_mono`: the canonical morphism of a domain is a
  monomorphism of `LocalizedCategory`. Write the source as a presentation
  `A` and the two parallel morphisms as images of morphisms `F` and `G` of
  `SourceCategory` (fullness). Faithfulness turns the equation in
  `LocalizedCategory` into `F ≫ ν = G ≫ ν`. Worker 36's monomorphism gives
  `F = G`.
- `exists_localizedDomainLift`: a morphism `f : X → S` of
  `LocalizedCategory` whose underlying map has image in `D` factors as
  `g ≫ ν`. Write `f` as the image of `F` and apply
  `SourceCategory.exists_domainFactor` to `F`. Its hypothesis concerns the
  underlying map of `F`, which is by definition that of `f`, since
  `SourceCategory.spaceFunctor` is `comparisonFunctor ⋙ localizedSpaceFunctor`.

The rest of the section states these facts for an arbitrary object `X` of
`LocalizedCategory` and a domain `D` of its presentation
`presentationOf X`. Here `presentationOf X` is the saturated presentation
with `localizationFunctor.obj (presentationOf X) = X`.

- `domainObj X D` is the analytic space of `D`. `domainι X D : domainObj X D ⟶ X`
  is the canonical morphism `ν`. `domainι_apply` says that its underlying map
  is the inclusion of the subspace, and `domainι_mono` says it is a
  monomorphism.
- `exists_domainLift`, and the chosen factorization `domainLift D f hf` with
  `domainLift_comp` (`domainLift D f hf ≫ domainι X D = f`) and
  `eq_domainLift` (uniqueness, from `domainι_mono`). This is Berkovich's
  "unique morphism ψ : Z → Y with φ = ν∘ψ". `val_domainLift_apply` says that
  the factorization has the underlying map of `f`, with its codomain
  restricted to `D`.
- `domainRestrict D E f hf : domainObj X D ⟶ domainObj Y E` is the restriction
  of `f : X ⟶ Y` to domains with `f(D) ⊆ E`, the factorization of
  `domainι X D ≫ f` through `E` (`domainι_comp_apply_mem` checks the image).
  `domainRestrict_comp` is the defining square. `domainRestrict_id` and
  `domainRestrict_comp_domainRestrict` say that restriction preserves
  identities and composition; both follow from uniqueness.

## Invariant domains and restricted actions

Let `G` be a monoid and `X : Action LocalizedCategory G` an action of `G` on
an analytic space.

- `IsInvariantDomain X D`: every `g ∈ G` maps `D` into `D`, that is, the
  underlying map of `X.ρ g` sends points of `D` to points of `D`.
- `invariantDomainAction X D hD` is the action of `G` on `domainObj X.V D` in
  which `g` acts by `domainRestrict D D (X.ρ g)`. The identity and
  multiplicativity (`map_one'`, `map_mul'`) follow from uniqueness of
  factorizations: `ν ≫ X.ρ 1 = ν` and
  `ν ≫ X.ρ (g h) = ν ≫ X.ρ h ≫ X.ρ g`, using Mathlib's convention
  `x * y = y ≫ x` in `End`. `invariantDomainAction_V` and
  `invariantDomainAction_ρ` record the object and the action.
- `invariantDomainInclusion X D hD` is `ν` as a morphism of actions, that is,
  an equivariant morphism. `invariantDomainInclusion_mono` says that it is a
  monomorphism of actions.
- `invariantDomainLift X D hD f hf` factors an equivariant morphism
  `f : Y ⟶ X` whose image lies in `D` through `D`, equivariantly, and
  `invariantDomainLift_comp` records the factorization. Equivariance is
  checked after composing with the monomorphism `ν`.

For a subgroup `H` of `G` that maps `D` into itself, apply these constructions
to the restriction `(Action.res _ H.subtype).obj X` of `X` to `H`. This
gives the action of the stabilizer on the domain, as in the quoted passages
of Berkovich and Harris.

## `G`-spaces

Let `G` be a topological group and `X : GSpace K G` a `G`-space: a Hausdorff
analytic space with an action of `G` that is continuous in Berkovich's sense
(`IsContinuousAction`, module `ContinuousAnalyticAction`).

- `invariantDomainGSpace X D hD hc` is the `G`-space of an invariant domain,
  given a proof `hc` that the restricted action is continuous. Its space is
  Hausdorff, being a subspace of the Hausdorff space of `X`.
- `invariantDomainGSpaceInclusion` is `ν` as a morphism of `G`-spaces.

The module `InvariantDomainContinuityStatement` states, as a Lean
proposition, that `hc` always holds.

## Scope

- The domains are those of the Library's model: subsets satisfying
  `IsOriginalChartDomain` for the charts of a saturated presentation. The
  comparison with all of Berkovich's analytic domains is discussed in
  `AnalyticDomainSpaces.md`; nothing more is claimed here.
- The factorization `domainLift` is chosen with `Classical.choose`. It is
  unique, so no choice is visible in its properties.
- An invariant domain is required to be mapped into itself by every element.
  For a group this already gives `g(D) = D`, because `g⁻¹` also maps `D` into
  `D`; this consequence is not formalized here.
