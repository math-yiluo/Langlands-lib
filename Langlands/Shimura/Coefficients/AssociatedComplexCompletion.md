# Ordinary completion comparison for associated coefficient complexes

This module constructs the canonical map from associated completed coefficient
complexes to the ordinary inverse limit of their associated coefficient quotient
complexes. It proves its naturality, quotient-projection equations, factorization
of the original quotient unit, uniqueness, and agreement in each degree with
the published ordinary associated-completion comparison.

## Input and scope

Let `R : Type u` be a commutative ring, `I : Ideal R`, and
`D : J ⥤ GrpCat.{u}` a diagram of groups, where the object and morphism universes
of `J` are independent. Let `X : Scheme.{u}`, and let
`Y : EquivariantDiagram D X.Etale` be a diagram of actual etale covers and deck
actions. At every index assume the published
`IsFiniteGeometricTorsor X (Y.action j)` predicate: the group and cover are finite,
the cover is surjective, and a unique deck translation relates geometric points
over the same base point. These hypotheses are used by the existing varying-cover
association functor.

The scheme, ring, module and group carriers share universe `u`. The complex
degree type `ι : Type uι` has an independent universe, and `c : ComplexShape ι`
is arbitrary. Write

```text
E = EquivariantDiagram D (ModuleCat R)
S = J ⥤ Sheaf X.smallEtaleTopology (ModuleCat R)
A : E ⥤ S
```

for the actual varying-cover associated-sheaf functor. Its proved additive
prolongation to `HomologicalComplex E c` is denoted here by `A_c`.
`DiagramAdicComplex` supplies the actual ideal-power reduction functors `P_n`,
degreewise compatible-sequence completion `C`, quotient units `q_n`, completion
unit `η`, and completion evaluations `p_n`, all on coefficient complexes.
The ring and ideal are arbitrary; the power index is the full `ℕᵒᵖ`, including
power zero, while `D` remains fixed.

## Associated quotient-complex system

`etaleAssociatedComplexPowerSystems` first forms the full coefficient
quotient-complex diagram and then postcomposes it with `A_c`. Its value at a
coefficient complex `K` is the inverse system `n ↦ A_c(P_n K)`. Its transitions
and its action on a coefficient chain map are the actual maps obtained by
association.

The four component equations
`etaleAssociatedComplexPowerSystems_obj_X`,
`etaleAssociatedComplexPowerSystems_obj_d`,
`etaleAssociatedComplexPowerSystems_transition_f`, and
`etaleAssociatedComplexPowerSystems_map_app_f`
identify its degree objects, differentials, transition components, and
coefficient-chain-map components. Each differential is
`A.map (P_n.map (K.d i j))`; each power transition and each coefficient map is
mapped through the same functors. These formulas follow by unfolding the actual
complex prolongations. Square-zero, shape and chain-map equations are inherited
from those constructions.

`etaleAssociatedComplexPowerLimit` takes the ordinary limit of this system
in `HomologicalComplex S c`. Pinned Mathlib's
`HomologicalComplexLimits` constructs these limits from the degreewise limits
in `S`, with differentials induced by `limMap` and actual projection chain maps.
The required limits in `S` exist through the sheaf and functor-category
instances. No limit-preservation assumption on `A` or `A_c` is introduced.

## Completion comparison

`etaleAssociatedCompletedComplexFunctor` sends `K` to `A_c(C(K))`.
`etaleAssociatedComplexCompletionCone` maps the genuine coefficient completion
cone through `A_c`. Its leg at `n` is exactly `A_c.map (p_n.app K)`, as recorded
by `etaleAssociatedComplexCompletionCone_π`.

`etaleAssociatedComplexCompletionComparison` is the natural transformation

```text
A_c(C(K)) → lim_n A_c(P_n K).
```

Its component is the universal lift from that mapped cone. Naturality is proved
by testing equality against every limit projection, applying the lift and
`limMap` projection equations, and using naturality of the actual completion
evaluations. Thus it is a natural family of genuine chain maps.

`etaleAssociatedComplexCompletionComparison_π` proves that its composite with
the `n`th limit projection is `A_c.map (p_n.app K)`.
`etaleAssociatedComplexCompletionComparison_unique` proves that these projection
equations characterize it among chain maps with the same source and target,
using the ordinary limit's uniqueness property.

Independently, `etaleAssociatedComplexPowerCone` uses the actual quotient maps
`A_c.map (q_n.app K)` as legs. Their compatibility follows from the coefficient
quotient-unit transition equation. Its universal lift is the natural
`etaleAssociatedComplexPowerLimitUnit`, whose projections are those quotient
maps by `etaleAssociatedComplexPowerLimitUnit_π`. Naturality is proved against
all limit projections using naturality of `q_n`.

`etaleAssociatedComplexCompletionComparison_unit` proves

```text
A_c.map (η.app K) ≫ comparison.app K = powerLimitUnit.app K.
```

This is equality of natural transformations. Its proof tests the components
against every projection and uses the previously proved coefficient-complex
identity `η ≫ p_n = q_n`.

## Degree evaluation

For each `K` and degree `i`,
`etaleAssociatedComplexPowerLimitDegreeIso` identifies the degree object of the
complex limit with the published ordinary coefficient-power limit at `K.X i`:

```text
(lim_n A_c(P_n K)).X i ≅ lim_n A(P_n(K.X i)).
```

It is Mathlib's `preservesLimitIso` for homological-complex evaluation, which
preserves these limits. The evaluated power system reduces to the ordinary
coefficient-power system. The theorem
`etaleAssociatedComplexPowerLimitDegreeIso_hom_π` says its homomorphism followed
by the ordinary `n`th projection equals the degree-`i` component of the complex
projection.

`etaleAssociatedComplexCompletionComparison_degree` proves that the degree-`i`
component of the new comparison, followed by this isomorphism, is exactly
`etaleAssociatedCompletionComparison` evaluated at `K.X i`. The source objects
agree by the definitions of associated complexes and degreewise completion.
The proof uses ordinary limit extensionality, the degree-isomorphism projection
equation, and the projection equations of the two comparisons.

## Provenance and remaining obligations

This is an internally derived categorical construction. Its mathematical inputs
are the published actual functors and proved intrinsic equations in
`AssociatedComplex`, `DiagramAdicComplex`, and `VaryingCoverCompletion`, with their
transitive coefficient, torsor and sheaf constructions. Pinned Mathlib
`Algebra/Homology/HomologicalComplexLimits.lean` supplies degreewise limits and
preservation by evaluation;
`CategoryTheory/Limits/Preserves/Limits.lean` supplies the canonical preservation
isomorphism and its projection equation. All new maps are constructed from these
inputs by functoriality and the ordinary limit universal property. No new
external theorem or literature definition is asserted.

The unit concerns ordinary complexes and ordinary inverse limits. It does not
establish that either comparison is invertible, that association preserves
infinite limits, or any exactness, derived completion, cohomology comparison,
topological or smooth action, lisse-adic property, or Harris-specific
identification. Those remain separate obligations of the larger framework.
