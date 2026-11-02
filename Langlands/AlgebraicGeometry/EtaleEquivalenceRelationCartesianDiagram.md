# Cofiltered diagrams of cartesian relation morphisms

Author: Worker 706.

This is an internal categorical interface for the action descent step in
Stacks Project Proposition 70.8.1, Tag 07SU, registered as
`stacks-noetherian-approximation-2026-11-01`. It organizes supplied data;
it does not assert that any approximation system exists. All relations,
schemes, index objects and index morphisms retain the arbitrary universe `u`.

`CartesianMorphism E F` bundles an object-scheme map, an arrow-scheme map,
and the existing `IsCartesianHom` property. The `ext` lemma says that its
two maps determine this bundle. Identity and composite cartesian
morphisms were already proved in Geometry. Using those results, the
category instance makes étale equivalence relations a category with
these morphisms. Its laws are the two scheme category laws, component by
component. `id_objMap`, `id_relMap`, `comp_objMap` and `comp_relMap`
record the component formulas.

`objectFunctor` and `relationFunctor` take a relation to its object
scheme and arrow scheme, respectively. They take a cartesian morphism
to its corresponding component. `sourceTransformation` and
`targetTransformation` are the two natural transformations between these
functors. Their naturality equations are the source square's commuting
equation and the target compatibility in `IsCartesianHom`.

In the `CartesianDiagram` namespace, `above D i` restricts a supplied
diagram to the over category of arrows into a fixed index `i`.
`comparison` maps each such level to `D_i` by its designated index arrow;
composition in the original diagram proves naturality.
`objectComparison` gives its object-scheme component.
`cone_comparison` states the compatibility of a supplied cone's object
legs with this comparison. It follows by applying the object component
to the cone equation at the designated index arrow.

If the original indexing category is cofiltered, Mathlib proves that
`Over i` is cofiltered and the forgetful functor `Over i → I` is initial.
`isLimitObjectAbove` uses this initiality to preserve a supplied
object-scheme limit cone when restricting above `i`. This is a limit
statement for a supplied cone, with no claim that a limit in the new
category of cartesian relations has been constructed.
