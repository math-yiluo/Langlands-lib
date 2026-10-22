# Induction category compatibility checks

Worker 15's intrinsic checks accompany the transparent reuse of Worker 23's
canonical category in
[`Induction/Definitions`](Definitions.md). They introduce no mathematical
construction, category instance, comparison equivalence, or additional
assumption. Their provenance is the definitions of the two category names and
the existing induction interfaces.

The unapplied constants `@Langlands.Induction.SmoothRep.{uR,uG,uV}` and
`@Langlands.SmoothRep.{uR,uG,uV}` are equal by `rfl`. This checks their entire
telescope, including explicit type arguments, inferred instances and the three
independent universes. A second `rfl` checks the former type expression
`ObjectProperty.FullSubcategory (fun A : Rep.{uV} R G => IsSmooth A.ρ)`.
These examples assume only a commutative coefficient ring, a group and a
topology on that group. In particular, they assume no continuity of its
operations. The inherited `Category`, `Preadditive` and `Linear R` instances
are checked by reflexivity as well.

Four explicit universally quantified type assignments check
`smoothInductionFunctor`, `compactInductionFunctor`,
`normalizedSmoothInductionFunctor` and `normalizedCompactInductionFunctor`.
They retain the independent coefficient, group and input-carrier universes,
the actual subgroup `P`, and target carrier universe `max uG uV`.
Normalized functors still take an actual `SmoothCharacter R P`.
The `IsTopologicalGroup G` instance belongs to these induction constructions
and is not added to the category alias.

Two further full type assignments check `smoothInducedMap` and
`compactInducedMap`, with independent universes for their source and target
modules. Four morphism formulas, all proved by `rfl`, check that the canonical
category's `SmoothRep.hom` recovers the existing map constructors. For the
normalized functors these are exactly the maps obtained by first applying
`twistIntertwining` with the supplied character.

These checks inspect the implemented definitions rather than asserting a new
independent theorem. The original mathematical source references and the
old-name-to-canonical-name map are retained in
[`Induction/Definitions`](Definitions.md) and
[`Category/Basic`](../Category/Basic.md). Existing consumer modules retain
their import paths and mathematical statements.
