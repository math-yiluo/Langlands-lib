# Cohomology of natural cocycles on a fixed cover

This internal construction gives the Library's natural cocycles the equivalence
relation used by `NumberFieldHassePrincipleStatement`. It introduces no arithmetic
local-to-global assertion.

For a group scheme `G` over any scheme `S : Scheme.{u}` and any object `U` over
`S`, `Cocycle.Cohomologous ξ ζ` means that there is a morphism `f : U ⟶ G.X`
with

`ζ(a,b) = f(a)⁻¹ ξ(a,b) f(b)`

on every pair of points of `U` over every scheme over `S`. This uses exactly
the twist convention of `TorsorCocycle`, including the order of multiplication.
No commutativity, smoothness, affineness, field, or covering assumption is needed
to define the relation.

`Cocycle.cohomologySetoid G U` packages this relation as a setoid. Reflexivity
uses the unit cochain, symmetry uses the inverse cochain, and transitivity
uses the product of the two cochains in the order in which the twists are
applied.

The accompanying naturality lemmas preserve the relation under group
homomorphisms, refinement of the cover, and arbitrary change of base with a
compatible cover. The base-change cochain is obtained by applying the inverse of
`baseChangePointsEquiv` to the restricted original cochain.

`Cohomologous.of_refine` reflects the relation along a refinement `r : V ⟶ U`
whose underlying scheme morphism is an effective epimorphism and whose square
product is an epimorphism. On two points of `V` with the same image in `U`,
both original cocycles evaluate to one. The twist identity therefore says that
the two restrictions of the witnessing cochain agree. Effective epimorphism
descent gives a cochain on `U`; epimorphy of the product refinement proves its
twist identity on the universal pair of points, hence on every test scheme.
`cohomologous_refine_iff` specializes this to a quasi-compact, flat, surjective
refinement, using the published `effectiveEpi_tensorHom`.

The provenance is internal: this is the orbit relation of the already published
`Cocycle.twist`, with a descent argument extending the published proof of
`Cocycle.isTrivial_refine_iff` from triviality to a pair of cocycles.
The implementation imports `CocycleRelativeTrivialization`, which imports
`CocycleRefinement` and `TorsorCocycle`. All universes are arbitrary.

`isTrivial_of_section` gives a trivialization of a cocycle when its cover has a section.
