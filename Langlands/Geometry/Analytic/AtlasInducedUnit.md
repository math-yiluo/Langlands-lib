# The normalized unit for induced arbitrary atlas actions

Author: Worker 56. Namespace: `Langlands.Analytic.AtlasInducedAction`.

This internal construction supplies the actual bounded unit from the
same-space nonempty-chart restriction of any supplied categorical subgroup
action. The field `K : Type u` is complete, normed and ultrametric;
`G : Type z` is a group and `H` is any subgroup. Presentations are in
`AffinoidAtlasPresentation.{u, max z v, max z w} K`. Original charts may
overlap or be nested, and spaces and chart-index types may be empty.

`normalizedAction H X` applies the existing nonempty-chart action functor.
It retains the original space, every original nonempty chart with its
original algebra and restrictions, and the original action's bounded maps
on those charts. The published `identityCoset` and `identityRepresentative`
are reused: write `c₀ = H` and `r₀ = c₀.out ∈ H`. The representative need
not equal one. `unitMap H X` first applies `localAction r₀⁻¹`, then the full
copy inclusion at `c₀`. Its exact point formula is `(c₀, r₀⁻¹ • x)`.
Its chosen chart target is the original inverse-representative action's
target, tagged by `c₀`, and its actual bounded pullback is precisely the
original pullback `(X.ρ r₀⁻¹).pullback i.val`.

The correction at the identity coset is `r₀⁻¹ * h * r₀` for `h ∈ H`.
Using this equation and the full action composition laws proves
`unitMap_equivariant`. Thus `unitEquivariantMap` is an actual arrow of
subgroup actions. The published identities
`c.out • c₀ = c` and `κ(c.out,c₀) = r₀` prove `unitMap_action`:
translating this unit by `c.out` recovers the entire inclusion of copy `c`.
This is full chosen-arrow equality, including bounded pullbacks.
Naturality follows from the original equivariant map's normalized
commutation equation and the proved `copy_map` equation.
`unitNat` packages the resulting natural transformation from
`nonemptyActionFunctor H` to `copiesFunctor H` followed by restriction.
It is not a transformation from the identity on all original presentations.

For a topological group, an open `H` and the specific hypothesis
`ContinuousSMul H (LocalSpace H X)`, `quotientUnitMap` composes this unit
with the constructed `copiesIso` into the actual balanced-quotient atlas.
Its full subgroup equivariance follows from that of the unit and the
transport isomorphism. `quotientUnitEquivariantMap` packages the actual
bounded arrow. The quotient balancing equation then proves
`quotientUnitMap_baseMap`: its point map is exactly `x ↦ [1,x]`,
independently of the chosen representative.

The provenance is internal. The implementation reuses the representative
identities of `GeneralizedAffinoid.InducedUnit` and
`GeneralizedAffinoid.InducedFamilyExtension`, but constructs its arrows from
the original arbitrary-atlas action, complete copy inclusions and transport
isomorphism. The laws are derived from the complete-arrow action and
functor equations; no output unit or factorization property is assumed and
no bounded-map equality is inferred from points. This supplies a unit for
the normalized source only: removing empty charts generally has no inverse
in the chosen-chart category. An unrestricted original-source unit or
adjunction is not claimed. Arbitrary-target extension and its Hom
correspondence, quotient functoriality, analytic automorphism continuity,
refinement localization and analytic sites remain separate obligations.
