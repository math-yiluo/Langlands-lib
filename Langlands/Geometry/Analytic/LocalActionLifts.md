# Lifts of group actions to compact quasi-étale and distinguished étale objects

Author: Worker 21.

Berkovich's equivariant sheaves on a `G`-space `X` use, for each quasi-étale
morphism `U → X` with compact `U` and for each distinguished étale morphism
`U → X`, a continuous action of an open subgroup `G_U ⊂ G` on `U` lifting the
action on `X`. Sections over `U` then carry an action of `G_U`, and smoothness
of a sheaf means that these actions are discrete. This module defines the
data of such lifts, compact analytic spaces and distinguished étale
morphisms. The existence and uniqueness of the lifts (a consequence of
Berkovich's Key Lemma) are not proved here.

## Original source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(unfinished manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`; file
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`),
§1.4, printed p.7:

> Recall that the Key Lemma 7.2 from [Ber3] implies that given a quasi-étale
> morphism U → X with compact U there exist ε ∈ 𝔈(X), δ ∈ 𝔈(U) and a unique
> continuous homomorphism 𝒢_ε(X) → 𝒢_δ(U) such that the morphism U → X
> commutes with the action of 𝒢_ε(X). It follows that for any quasi-étale
> morphism U → X with compact U the action of G on X extends in a canonical
> way to a continuous action of some open subgroup G_U ⊂ G on U. Furthermore,
> an étale morphism 𝒰 → X is said to be distinguished if it can be
> represented as a composition 𝒰 ↪ U → X (arrows labelled j and φ), where U
> is compact, φ is quasi-étale and j identifies 𝒰 with a distinguished open
> subset of U, i.e., with such one whose complement in U is an analytic
> domain. For such a morphism the action of G on X extends in a canonical way
> to a continuous action of an open subgroup G_U ⊂ G. Since U∖𝒰 is a compact
> analytic domain in U, then 𝒰 is invariant under the action of an open
> subgroup G_𝒰 ⊂ G_U. If there is another representation of the morphism
> 𝒰 → X as a composition 𝒰 ↪ U′ → X and, therefore, an extension of the
> action of G on X to a continuous action of an open subgroup G′_𝒰 ⊂ G on 𝒰,
> then one can find an open subgroup N ⊂ G_𝒰 ∩ G′_𝒰 such that the two
> actions of N on 𝒰 coincide.

In the original, `𝒰` (calligraphic) is the distinguished étale object and
`U` the compact space containing it. Below, the Lean names are `U` for the
source of the étale morphism and `Ubar` (written `Ū`) for the compact space.

Here [Ber3] is Berkovich, *Vanishing cycles for formal schemes* (1994),
registered as `berkovich-1994-vanishing-cycles-formal-schemes`, SHA256
`f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`, Key
Lemma 7.2, printed p.560.

Compactness includes Hausdorffness: Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), registered as
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`, §1.1,
printed p.13 / PDF p.10: "All compact, locally compact and paracompact spaces
are assumed to be Hausdorff."

## Definitions

All declarations are in `Langlands.Analytic.SaturatedAtlasPresentation`. The
field `K` is a complete ultrametric normed field (trivial valuation allowed);
spaces are objects of `LocalizedCategory.{u, v, v}`, as in `EtaleSite`. The
group `G` has a topology.

- `IsCompactSpace U`: the underlying space of `U` (`localizedSpaceFunctor`)
  is compact and Hausdorff.
- `ActionLift ρ f`, for an action `ρ : G →* Aut X` and a morphism
  `f : U ⟶ X`, is a structure with
  - `subgroup`: a subgroup `H` of `G`, with `isOpen_subgroup`;
  - `action : H →* Aut U`, with `isContinuousAction`: continuity in the sense
    of the Library's `IsContinuousAction` (Berkovich's topology on `G(U)`
    through the test relations of `E(U)`; `H` has the subspace topology);
  - `equivariant`: `(action h).hom ≫ f = f ≫ (ρ h).hom` for every `h ∈ H`, so
    `f` commutes with the actions.

  This is the data "the action of G on X extends … to a continuous action of
  some open subgroup G_U ⊂ G on U".
- `ActionLift.AgreeOn a b N`: `N` is an open subgroup contained in the
  subgroups of both lifts, and the two actions agree on `N`. This is the
  relation in the last sentence quoted above.
- `ActionLift.restrict a N hN hle`: restriction of a lift to an open subgroup
  `N ≤ H`. Continuity follows from `IsContinuousAction.comp` for the
  continuous inclusion `N → H`; equivariance is inherited.
  `restrict_action_apply` records the restricted action.
- `IsDistinguishedEtale f`, for `f : U ⟶ X`: `f` is étale, and there are a
  compact space `Ū` (`IsCompactSpace`), a quasi-étale `φ : Ū ⟶ X`
  (`quasiEtale`), analytic domains `O` and `D` of the saturated presentation
  underlying `Ū` with `O` open and `D` the complement of `O`, and an
  isomorphism `e` from `U` to the analytic space of `O` with
  `f = e.hom ≫ ν_O ≫ φ`, where `ν_O` is the canonical morphism of the
  domain (`localizedDomainInclusion`). This is Berkovich's distinguished
  étale morphism `U ↪ Ū → X`, with `j = e.hom ≫ ν_O` identifying `U` with the
  distinguished open subset `O`.

Provenance. The structure `ActionLift` and the predicates transcribe the
quoted passage. Derived choices:

- Continuity of the lifted action is the Library's `IsContinuousAction` for
  the subgroup with its subspace topology. When `G` is a topological group,
  `H` is one as well, and this is Berkovich's continuity of `H → G(U)`.
- The open subset `O` is required to be an analytic domain of the chosen
  presentation of `Ū`. Berkovich's spaces have a dense class of affinoid
  domains, so every open subset is an analytic domain (1993, remark after
  Definition 1.3.1, printed p.23: "If the class Φ_k is dense, then all open
  subsets of X are Φ-analytic domains"); with charts of the saturated
  presentation in place of affinoid domains, as in `AnalyticDomainSpaces`,
  this is an explained but not formalized comparison.
- Compactness and the quasi-étale and étale conditions are those of the
  Library's `IsCompactSpace`, `quasiEtale` and `etale`.

## Scope

Not done here: existence of lifts for compact quasi-étale and distinguished
étale morphisms and their uniqueness up to `AgreeOn` (the consequences of the
Key Lemma); the Key Lemma itself; the canonical choice `G_U`; the induced
actions on sections and the smoothness condition of Definition 1.4.1, which
belong to the equivariant sheaf branch of the parent task.
