# The actual normal-quotient coinvariant functor

Source: Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, III.2.10, printed pp.80–82 / PDF pp.86–88.
The group quotient carries its quotient topology.

For a normal subgroup `N` of a topological group `P`, `normalQuotientAction`
is exactly Mathlib's `Representation.quotientToCoinvariants`. Its carrier
is the already published `Jacquet.Coinvariants ρ N`, the quotient of the
original module by the span of `ρ(n)v − v`. Its action satisfies

`q(p) · [v] = [ρ(p)v]`.

There is no supplied descended action or replacement quotient. The helper
`normalQuotientAction_mk` exposes this definitional representative formula.

`isSmooth_normalQuotientAction` first uses the original surjective quotient
map to obtain smoothness as a `P` representation. The stabilizer of a
quotient vector in `P` is the preimage of its stabilizer in `P/N`. By the
quotient topology, openness of this preimage gives openness downstairs.
No closedness or local compactness is needed for this smoothness argument.

`normalCoinvariantFunctor` bundles these actual actions and the maps of
Mathlib's `Rep.quotientToCoinvariantsFunctor`. On a morphism `f`, it sends
`[v]` to `[f(v)]`, as recorded by `normalCoinvariantFunctor_map_mk`.
Functoriality is inherited from that existing algebraic functor.
The coefficient, group and carrier universes are independent.

The auxiliary `quotientOpenSubgroup` is the image of an open subgroup under
the open quotient map; compactness is its continuous-image property.
`quotientNonarchimedean` registers the published
`Langlands.LocalClassField.quotientNonarchimedean` theorem as an instance;
its proof uses images of the original open subgroup basis. These are the elementary
quotient-topology ingredients used at the start of III.2.10. For the source's
closed normal subgroup in a Hausdorff locally compact nonarchimedean group,
the existing quotient instances also give Hausdorffness and local compactness.

This unit constructs `j_N`. Its comparison with Hecke tensor induction,
the adjunctions and the formulas (III.2.10.1)–(III.2.10.2) are separate
statement targets; no proof of those comparisons is claimed here.
