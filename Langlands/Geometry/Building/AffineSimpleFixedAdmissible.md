# The simple reflections fixing a point form an admissible type

Fix `hΨ : IsAffineRootSystemWithRankZero Ψ` on a real affine space `A` over `V`
(independent universes `uV`, `uA`), and a chamber `C` (`IsChamber Ψ C`). Write
`S = chamberSimpleReflections Ψ C` for the existing geometric simple
reflections of `C`, as elements of `affineWeylGroup Ψ`. This module proves that
for every point `x` the simple reflections fixing `x` form an admissible type,
`IsAdmissibleType S X`. In the existing convention (KP Definition 1.5.17(1))
this means that `X ⊆ S` and every `s ∈ S` has an element `t ∈ S` of its
irreducible component (`SameComponent S s t`, the reflexive transitive closure
of noncommutation) outside `X`. The facet-simple reflections of any facet
therefore form an admissible type.

Source correspondence: in the proof of KP Proposition 7.5.6(2) (book
pp. 262–263), the facets of `C` correspond to the admissible types. KP first
treats the irreducible case, where facets of `C` correspond to proper subsets
of the simple reflections, and then reduces the general case to it through the
product decomposition of the group and of `C`. This module proves the
direction "types of facets are admissible" directly, with no irreducible
decomposition. It is an internal deduction from the existing affine-root,
reflection and restricted-Tits APIs, and it introduces no external assertion.

## Definitions and elementary lemmas

`fixingSimpleReflections Ψ C x` is the set of `s ∈ S` with `s x = x`.
`mem_fixingSimpleReflections` unfolds it, and `fixingSimpleReflections_subset`
records that it lies in `S`.

`affineReflection_apply_eq_self_iff`: an affine reflection `x ↦ -ψ(x) • v +ᵥ x`
fixes `y` exactly when `ψ y = 0`. One direction is
`apply_affineReflection`, the other `affineReflection_apply_of_mem`.

`apply_affineReflection_of_linear_eq`: if `η` has the same derivative as `ψ`
and coroot vector `w`, then `ψ(r_η y) = ψ(y) - 2 η(y)`.

`eq_of_linear_eq_of_apply_eq_zero`: two affine functionals with the same
derivative vanishing at a common point are equal.

`setPreserving Ψ L` is the subgroup of `affineWeylGroup Ψ` of elements `w`
with `y ∈ L ↔ w y ∈ L` for all `y`. It is closed under products, and under
inverses because `w (w⁻¹ y) = y`.

`facetSimpleReflections_facet_eq` proves that the existing
`facetSimpleReflections Ψ C (facet Ψ x)` (reflections of simple roots vanishing
on the facet of `x`) equals `fixingSimpleReflections Ψ C x`. A simple root
vanishing at `x` vanishes on the whole facet, because facet-related points
have the same root signs.

## The main argument

`isAdmissibleType_fixingSimpleReflections`: suppose some `s ∈ S` has its
whole component inside `X = fixingSimpleReflections Ψ C x`. Let `L` be the set
of points fixed by every `k ∈ S` in the component of `s`. Then `x ∈ L`.

Every `t ∈ S` maps `L` into `L`. If `t` is in the component of `s`, it fixes
every point of `L`. Otherwise `t` commutes with every `k` in the component,
since noncommutation would put `t` in the component (`ReflTransGen.tail`).
Then `k (t y) = t (k y) = t y`. Each `t ∈ S` is an involution, so `S` lies in
`setPreserving Ψ L`. Hence the whole group `closure S`, which is all of
`affineWeylGroup Ψ` by the existing `closure_chamberSimpleReflections`, does.

Write `s = r_ψ` for a simple root `ψ` with coroot `v`. The existing
`exists_noncommuting_parallel_reflection` (from corrected AR4) gives a root
`η ≠ ψ` with `η.linear = ψ.linear` and its reflection `t = r_η` in the affine
Weyl group. Then `t x ∈ L`, so `s` fixes `t x` and `ψ(t x) = 0`. Also `s`
fixes `x`, so `ψ(x) = 0`. Hence `0 = ψ(t x) = ψ(x) - 2 η(x) = -2 η(x)`, so
`η(x) = 0`. By `eq_of_linear_eq_of_apply_eq_zero`, `η = ψ`, a contradiction.

`isAdmissibleType_facetSimpleReflections` combines this with
`facetSimpleReflections_facet_eq`: for every facet `Fa`,
`IsAdmissibleType S (facetSimpleReflections Ψ C Fa)`.

## Scope

These results concern one chamber of an abstract affine root system, rank
zero allowed. They do not prove the converse (that every admissible type is
the type of a face of `C`), finiteness of the generated subgroups, or any
comparison with parahoric subgroups. They prove no witness of
`RootValuationBuildingConstructionStatement`.
