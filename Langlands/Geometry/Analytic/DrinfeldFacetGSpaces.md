# Harris's domains `U(f)` as `H`-spaces, given continuity of the action

Author: Worker 21.

This module makes Drinfeld's upper half space `Ω` a `GL_{d+1}(F)`-space, and
Harris's domain `U(f)` an `H`-space for every subgroup `H` of the stabilizer
`S(f)`, in the sense of Berkovich: Hausdorff analytic spaces with a continuous
action of a topological group. Continuity is not proved here. Each
construction takes the continuity of its action as a hypothesis, and the module
proves that the hypotheses follow from two published statements that are
still unproved. All declarations lie in
`Langlands.Analytic.DrinfeldUpperHalfSpace`. Everything stated in the module is
proved.

The underlying actions are constructed in earlier modules. `omegaAction F K d`
(module `DrinfeldGroupAction`) is the action of `GL_{d+1}(F)` on `Ω`.
`facetAction K hS ε H hH` (module `DrinfeldFacetSpaces`) is the action of
`H ≤ S(f)` on the open domain `U(f) = Res⁻¹(B(f, ε))`, for a finite set `f` of
vertices of the building. The category `GSpace K G` of `G`-spaces and
`G`-morphisms, its restriction functor `GSpace.res` and continuity
`IsContinuousAction` are those of `ContinuousAnalyticAction`. The general
construction `invariantDomainGSpace` is in `InvariantAnalyticDomains`.

## Original sources

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`), §1.1,
printed p.2:

> An analytic space X endowed with a continuous action of a topological group
> G will be called a G-space. A G-equivariant morphism between two G-spaces
> will be called a G-morphism.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, §2,
printed pp.303–304 (PDF page = printed page − 298):

> Recall that the action of G_J on Ω lifts to an action on ℳ_N, and U(ê) is
> stabilized by a compact open subgroup S(ê) ⊂ G_J. That S(ê) is compact was
> not stated explicitly in [H1], but it follows from the fact that S(ê)
> stabilizes a facet of the building BT and is contained in the kernel of
> g ↦ |χ(g)| where χ is any algebraic character of G_J and | · | is the p-adic
> absolute value.

Harris then applies Berkovich's equivariant constructions to the action of
`S(ê)` on `U(ê)`. Here `ê = (e, N, δ)` and `U(ê)` lies in the level-`N`
covering `ℳ_N` of `Ω × Δ` (printed p.303), which is not constructed in the
Library. This module covers the domains `U(e)` of `Ω` itself.

Harris's group (printed p.303, first display) is the product
`G_J = (∏_j B(F_j)^×) × ℚ_p^×`, where `F = F_1` and `B(F)` is the matrix
algebra. Only its factor `B(F)^×`, the matrix group `GL_{d+1}(F)`, is
constructed in the Library, together with its action `omegaAction` on `Ω`.
Neither `G_J`, nor its action on `Ω`, nor the building of `G_J^ad` is
constructed.

## Derived choices

1. All groups in this module are subgroups of `GL_{d+1}(F)`, the matrix
   factor `B(F)^×` of Harris's `G_J`, and not subgroups of `G_J`. The facets
   are those of the Library's building of norm classes of `F^{d+1}`, as in
   `DrinfeldBuildingCovering`. `S(f)` is the stabilizer in `GL_{d+1}(F)` of a
   finite set `f` of its vertices.
2. `facetStabilizerNormOne S` is the subgroup of `GL_{d+1}(F)` with the two
   properties Harris uses for `S(ê)`, stated for `GL_{d+1}(F)` in place of
   `G_J`. It consists of the elements of `S(f)` in the kernel of every
   `g ↦ |χ(g)|` for `χ` an algebraic character of `GL_{d+1}` over `F`. These
   characters are the integer powers of `det`, so the condition is
   `|det g| = 1`. This is an analogue in the matrix factor, not a statement
   about Harris's `S(ê)`. Since `S(ê)` is a subgroup of `G_J`, the module
   makes no comparison between `S(ê)` and `facetStabilizerNormOne`, and it
   defines no projection from `G_J` to `GL_{d+1}(F)`. That
   `facetStabilizerNormOne` is compact and open is not proved here.
3. Rather than asserting continuity, each `G`-space takes the continuity of
   its action as a hypothesis. The hypotheses are discharged by the published
   statements, as recorded below.

## Declarations

- `subgroupInclusion H`: the inclusion of a subgroup `H` of `GL_{d+1}(F)`, as a
  continuous homomorphism `H →ₜ* GL_{d+1}(F)` (`H` has the subspace topology).
  `subgroupInclusion_apply` gives its value.
- `facetStabilizerNormOne S`: the subgroup of elements `γ ∈ S(f)` with
  `|det γ| = 1`, the intersection of `S(f)` with the kernel of
  `γ ↦ |det γ|` (as a homomorphism to `ℝ^×`). `mem_facetStabilizerNormOne`
  characterizes membership; `facetStabilizerNormOne_le` says it lies in `S(f)`.
- `omegaGSpace K hΩ`: `Ω` as a `GL_{d+1}(F)`-space, given
  `hΩ : IsContinuousAction (omegaAction F K d).ρAut`. Its underlying action is
  `omegaAction F K d` (`omegaGSpace_obj`), and `Ω` is Hausdorff by the instance
  of `DrinfeldGroupAction`.
- `isContinuousAction_omegaAction K h`: the published statement
  `OmegaActionContinuityStatement` gives `hΩ` for every `F`, `K` and `d ≥ 1`.
- `isContinuousAction_facetAction hΩ hInv hS ε H hH`: given `hΩ` and the
  published statement `InvariantDomainContinuityStatement` (`hInv`), the action
  of `H ≤ S(f)` on `U(f)` is continuous. The proof applies `hInv` to the
  restriction of `omegaGSpace K hΩ` to `H` along `subgroupInclusion H`, the
  analytic domain `U(f)` of `Ω` (`facetAnalyticDomain`), and its invariance
  under `H` (`isInvariantDomain_facetAnalyticDomain`). The restricted action
  produced by `InvariantAnalyticDomains` is `facetAction` by definition.
- `facetGSpace K hS ε H hH hc`: `U(f)` as an `H`-space, given
  `hc : IsContinuousAction (facetAction K hS ε H hH).ρAut`. Its underlying
  action is `facetAction K hS ε H hH` (`facetGSpace_obj`), and `U(f)` is
  Hausdorff as a subspace of `Ω`.
- `facetGSpaceInclusion K hΩ hS ε H hH hc`: the inclusion `U(f) → Ω` as an
  `H`-morphism to the restriction of `omegaGSpace K hΩ` to `H`. Its underlying
  equivariant morphism is `facetInclusion` (`facetGSpaceInclusion_hom`).
- `facetGSpace_eq_invariantDomainGSpace`: `facetGSpace` is the general
  `invariantDomainGSpace` for the invariant domain `U(f)` of the restriction of
  `omegaGSpace K hΩ` to `H` (by definition).
- `facetStabilizerGSpace K hS ε hc`: for a facet `f`, `U(f)` as an
  `S(f)`-space.
- `facetNormOneGSpace K hS ε hc`: for a facet `f`, `U(f)` as a space with a
  continuous action of `facetStabilizerNormOne`.

Assumptions: `F` is a nontrivially normed field with `ProperSpace F` (so
locally compact), `K` is a complete ultrametric nontrivially normed field and a
normed `F`-algebra, and `d ≥ 1` (`NeZero d`), as for `omegaAction`.

## Scope

- Continuity itself is the content of the unproved published statements
  `OmegaActionContinuityStatement` and `InvariantDomainContinuityStatement`;
  this module does not assume them globally.
- The tower `ℳ_N`, its domains `U(e, N, δ)`, Harris's group `G_J` and its
  subgroup `S(ê)` are not constructed here.
