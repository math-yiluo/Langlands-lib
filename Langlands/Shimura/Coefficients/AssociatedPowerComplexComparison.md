# Comparing sheaf-power and associated coefficient-power complexes

Author: Worker 13.

This module constructs the canonical comparison from the sheaf-power quotient
complexes of an associated complex to the associated coefficient-power quotient
complexes. It proves naturality in the complete power system and coefficient
chain maps, compatibility with the genuine quotient units, and the induced
ordinary-limit comparison. In every degree the latter is the published
comparison of ordinary diagram limits.

## Inputs and conventions

Let `R : Type u` be a commutative ring, `I : Ideal R`, and
`X : Scheme.{u}`. Let `J : Type uJ` have morphisms in universe `vJ`,
`D : J ⥤ GrpCat.{u}`, and `Y : EquivariantDiagram D X.Etale`. The
construction assumes `hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j)`.
This is the published predicate requiring a finite group, a finite surjective
cover morphism, and a unique deck translation between geometric points above
the same base point; the cover objects are already etale. These hypotheses
enter through the actual varying-cover association functor.

The scheme, ring, group carriers and module carriers share universe `u`.
The cover-object and cover-morphism universes `uJ` and `vJ` and complex-degree
universe `uι` are independent. The degree type `ι : Type uι` and
`c : ComplexShape ι` are arbitrary. No topology on the groups is imposed.

Write

```text
E = EquivariantDiagram D (ModuleCat R)
S = J ⥤ Sheaf X.smallEtaleTopology (ModuleCat R)
A : E ⥤ S
```

for the published actual varying-cover associated-sheaf functor, and `A_c`
for its additive prolongation to complexes. Write `P_n` for the actual
coefficient power quotient and `Q_n` for the actual sheafified sectionwise
power quotient, both prolonged to complexes. On a section module `M`, the
latter uses `M / (I^n • ⊤)` and retains its `R`-module structure. The
coefficient quotients also retain `R`-scalars. The inverse-system index is
the full `ℕᵒᵖ`, including zero, with transitions from exponent `n` to
exponent `m` when `m ≤ n`. This index is independent of `J`; no limit over
`J` is taken.

## Actual system comparison

`etaleAssociatedSheafComplexPowerSystems` sends a coefficient complex `K`
to `n ↦ Q_n(A_c K)`. It composes the published associated-complex functor
with `sheafDiagramComplexReductionFunctor`. Thus its degree objects,
differentials, power transitions and maps of coefficient complexes are the
actual images under the sheaf-power quotient functors. The target system
`n ↦ A_c(P_n K)` is reused unchanged from
`etaleAssociatedComplexPowerSystems` in `AssociatedComplexCompletion`.

`etaleAssociatedComplexPowerComparison K n` is a chain map between the
two systems at exponent `n`. In degree `i` it is the existing whole-diagram
comparison
`((etaleAssociatedVaryingReductionSystemsComparison ...).app (K.X i)).app n`.
Its chain-map commutation equation follows from naturality of that comparison
in the actual differential `K.d i k`, evaluated at `n`. The square-zero and
shape fields of the source and target complexes are those already constructed
by their additive functors.

`etaleAssociatedComplexReductionSystemsComparison` assembles these chain maps
into a natural transformation between the two full power-system functors.
Power naturality is proved degreewise using the power naturality of the
published diagram comparison. Naturality in a coefficient chain map `f` is
proved degreewise using its naturality in `f.f i`.

The component formula
`etaleAssociatedComplexReductionSystemsComparison_app_f` identifies the map
in degree `i` and cover coordinate `j` at exponent `n` with exactly
`constantAssociatedPowerReductionComparison` on `(K.X i).action j`.
It is a definitional equality; no new pointwise comparison is assumed.

`etaleAssociatedComplexReductionSystemsComparison_unit` proves

```text
sheafQuotient_n(A_c K) ≫ comparison_n(K) = A_c.map (coefficientQuotient_n(K)).
```

The proof compares chain-map components and then cover components. Removing
the identity maps from the canonical identity-complex isomorphisms leaves
the published `etaleAssociatedVaryingPowerUnit_app` equation. In particular,
the left quotient is the genuine sheafification-counit/sectionwise quotient
map, and the right quotient is the actual coefficient-diagram quotient
chain map.

## Ordinary limits and quotient units

`etaleAssociatedSheafComplexPowerLimit` takes the ordinary categorical limit
of `n ↦ Q_n(A_c K)` in `HomologicalComplex S c`.
`etaleAssociatedSheafComplexPowerLimitUnit` is the natural unit induced by
the already constructed genuine sheaf quotient cone, precomposed with `A_c`.
Its projection equation
`etaleAssociatedSheafComplexPowerLimitUnit_π` identifies the composite
with the exponent-`n` projection as the actual sheaf quotient chain map.

`etaleAssociatedComplexPowerLimitComparison` applies the ordinary limit
functor to the constructed system comparison:

```text
lim_n Q_n(A_c K) → lim_n A_c(P_n K).
```

Its target is precisely the published `etaleAssociatedComplexPowerLimit`.
The theorem `etaleAssociatedComplexPowerLimitComparison_π` identifies its
composite with the target exponent-`n` projection as the source projection
followed by the actual exponent-`n` comparison. This follows from
`limMap_π`.

`etaleAssociatedComplexPowerLimitComparison_unit` proves that the sheaf
quotient-limit unit followed by this comparison is exactly the published
`etaleAssociatedComplexPowerLimitUnit`. The proof compares every limit
projection, applies the two unit projection equations, and uses the genuine
quotient-chain-map equation above.

`etaleAssociatedComplexPowerLimitComparison_unique` characterizes the map
among all chain maps with the same source and target by these complete
projection equations. It uses the uniqueness property of the ordinary
target limit.

## Degree evaluation

`etaleAssociatedSheafComplexPowerLimitDegreeIso` identifies degree `i` of
the source limit with the published ordinary sheaf-power limit of `K.X i`:

```text
(lim_n Q_n(A_c K)).X i ≅ etaleAssociatedSheafPowerLimit.obj (K.X i).
```

It specializes the published degree-evaluation isomorphism for arbitrary
sheaf-diagram complexes to `A_c K`. The evaluated power system agrees with
the published one by the actual definitions. The accompanying
`etaleAssociatedSheafComplexPowerLimitDegreeIso_hom_π` equation identifies
every projection with the degree component of the complex projection.

`etaleAssociatedComplexPowerLimitComparison_degree` proves the commutative
square

```text
comparison(K).f i ≫ coefficientLimitDegreeIso.hom
  = sheafLimitDegreeIso.hom ≫ etaleAssociatedPowerLimitComparison.app (K.X i).
```

The target degree isomorphism is reused from
`AssociatedComplexCompletion`. The proof compares all ordinary
coefficient-power projections and applies the two degree projection
identities and the original and constructed comparison projection
identities. The new comparison therefore agrees with the published
ordinary one in every degree, as a map of whole cover diagrams.

## Provenance and scope

This is internal categorical infrastructure derived from the actual
published definitions and proved intrinsic equations in
`AssociatedComplexCompletion`, `SheafDiagramAdicComplex`,
`VaryingCoverPowerSystems` and `VaryingCoverPowerLimits`.
The coefficient and sheaf quotients, their units, associated sheaves and
the original comparison are reused unchanged. New chain maps are
constructed from naturality in the actual differentials. New system laws
come from existing naturality; the limit maps and their uniqueness follow
from the ordinary limit universal property.

The underlying pinned Mathlib revision is
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0.
Its `Algebra.Homology.HomologicalComplex` supplies chain maps and their
extensionality. Its ordinary limit functor and projection equations are
in `CategoryTheory.Limits.HasLimits`; the degreewise complex limits and
evaluation-preservation isomorphisms are supplied through the imported
published modules by `Algebra.Homology.HomologicalComplexLimits` and
`CategoryTheory.Limits.Preserves.Limits`. No new theorem is attributed
to the original literature.

The construction concerns ordinary complexes and ordinary inverse limits
for arbitrary input torsor diagrams satisfying the stated predicate.
Invertibility of the comparison or units, exactness, preservation of
infinite limits by association, derived completion, cohomology comparison,
smooth or continuous actions, lisse-adic properties and identification
with Harris-specific objects remain separate obligations.
