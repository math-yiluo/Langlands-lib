# Native normal coinvariants and character-one subgroup localization

This internally derived construction compares the actual native normal
coinvariant action with the existing character-one localization action.
It works over every commutative ring, with independent coefficient, group
and carrier universes. It imposes no smoothness or finiteness assumptions.

For a representation `ρ` of `G`, a normal subgroup `N` and a subgroup `M`
normalizing `N`, `normalCoinvariantsLocalizationEquiv` identifies
`(ρ.toCoinvariants N).comp M.subtype` with
`Localization.action ρ N 1 M hMN (isInvariant_one N M hMN)`.
Its linear equivalence is the inverse of the published `trivialEquiv`.
Equality of the trivial-character relation span with the untwisted relation
span proves bijectivity. Both group actions send the class of `v` to the
class of `ρ(m)v`, which proves equivariance on representatives.
The forward and inverse representative formulas and naturality in every
native ambient intertwiner are proved explicitly.

For `U, M ≤ Q ≤ G`, retain the existing hypothesis that `M` normalizes `U`
and require that the literal nested subgroup `U.subgroupOf Q` be normal in
`Q`. For every native representation `ρ` of `Q`,
`normalCoinvariantsSubgroupEquiv` identifies

```text
(ρ.toCoinvariants (U.subgroupOf Q)).comp (Subgroup.inclusion hMQ)
```

with the representation underlying
`(Localization.Coefficient.subgroupFunctor U M hMU Q hUQ hMQ).obj (Rep.of ρ)`.
The target is the existing functor: it takes the literal character-one
quotient of the `Q` representation and pulls back the nested normalizing
action to the original ambient subgroup `M`. The construction uses the
preceding normal quotient equivalence for the nested subgroup. On each
representative the source inclusion and the target pullback apply the same
element of `Q`, so the comparison intertwines the original `M` actions.
Its two representative formulas and naturality in every native
`Q`-intertwiner retain the original quotient classes. The naturality formula
uses the underlying `Localization.mapLinear`, so the two inducing carriers
may have independent universes even though `Rep` as a category fixes one
carrier universe.

These comparisons follow from the already implemented quotient definitions
and the proved `Localization.trivialEquiv` and `subgroupFunctor` constructions.
They are internal transport results, with no claim that a source states
this Lean formulation verbatim. They identify existing quotient actions;
they prove no geometric comparison, measure existence, admissibility,
normalization cancellation or universal-family fixed-module finiteness.
