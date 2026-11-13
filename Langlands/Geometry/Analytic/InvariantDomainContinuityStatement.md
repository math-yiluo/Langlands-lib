# Invariant analytic domains of `G`-spaces are `G`-spaces

Author: Worker 21.

This module contains only a statement: the Prop-valued definition
`InvariantDomainContinuityStatement`. Nothing here proves it.

## Statement

For every complete ultrametric field `K`, every group `G` with a topology,
every `G`-space `X` (`GSpace K G`: a Hausdorff analytic space with an action of
`G` that is continuous in Berkovich's sense), and every analytic domain `D` of
`X` that every element of `G` maps into itself (`IsInvariantDomain X.obj D`),
the restricted action of `G` on `D` (`invariantDomainAction X.obj D hD`,
module `InvariantAnalyticDomains`) is continuous: it satisfies
`IsContinuousAction` for its action by automorphisms (`ρAut`).

With a proof of this statement, `invariantDomainGSpace` makes every invariant
domain of a `G`-space a `G`-space, with `ν : D → X` a morphism of `G`-spaces.

## Original sources

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.4, printed p.7 (PDF page = printed page), uses this property without
comment. After obtaining a continuous action of `G_U` on a compact `U`, it says:

> Since U∖𝒰 is a compact analytic domain in U, then 𝒰 is invariant under the
> action of an open subgroup G_𝒰 ⊂ G_U.

It then treats `G_𝒰` as acting continuously on `𝒰`. Harris, *Galois
properties of cohomological automorphic forms on GL(n)* (1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, §2, printed
pp.303–304 (PDF page = printed page − 298), likewise lets the stabilizer
`S(ê)` act on `U(ê)` and applies Berkovich's equivariant constructions to
that action.

Continuity is Berkovich's: §1.1, printed pp.1–2, gives the relations
`d(φ, ψ) < ε` for `ε ∈ E(X)`, the subgroups `G_ε(X)`, and says that an action
`G → G(X)` is continuous if this homomorphism is continuous. The Library's
form is `IsContinuousAction` in `ContinuousAnalyticAction`: for every test
triple `τ = (U, f, t)`, with `U` a chart, the set of `g` with
`d(ρ(g), 1) < τ` is a neighbourhood of `1`.

## Why the statement is expected to hold

The following argument is derived (it is not in the sources) and is not
formalized. Let `τ = (U, f, t)` be a test triple of `D`: a chart `U` of `X`
contained in `D`, a function `f` on `U`, and `t > 0`. The same data form a
test triple `τ_X` of `X`. If `g` is in Berkovich's subgroup `G_{τ_X}(X)`, then
`ρ(g)` maps `D` onto `D` and `U ⊆ D`, so the preimage of `U` under the
restriction of `ρ(g)` to `D` is the preimage under `ρ(g)`. The pullbacks of
`f` along the restricted maps are the pullbacks along `ρ(g)`, so `g` is in
`G_τ(D)`. Hence the preimage of `G_τ(D)` contains the preimage of
`G_{τ_X}(X)`, which is a neighbourhood of `1` by continuity of the action on
`X`.

In the Library's terms, `IsNear` is witnessed by right fractions `s⁻¹a`,
`s⁻¹b` with `StrongNear τ_X a b`. A witness for the restriction is obtained
from the inverse-image domain `s⁻¹(D)` (Worker 36's
`SourceCategory.domainPreimage`), refined to charts that `a` and `b` send into
charts contained in `D`. The covering pieces of `StrongNear τ_X a b` are
charts sent into `U ⊆ D` by both maps, so they survive this refinement, and
the bounds are unchanged.
