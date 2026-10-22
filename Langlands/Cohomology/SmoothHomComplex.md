# Hom complexes of actual smooth representations

Author: Worker 13.

This module instantiates the companion linear Hom construction in the
published category `Langlands.SmoothRep R G`, imported from
`Langlands.Representation.Category.Basic`. That category consists of actual
representations with proved open-subgroup smoothness; its morphisms are
equivariant linear maps. The category is reused without modification.

`bifunctor` constructs the module-valued Hom complex between two given
integer-graded complexes of smooth representations. Its degree `n` terms
are products of the equivariant morphism modules in the appropriate degrees.
The companion supplies the differential, its square-zero law, and functorial
chain maps in both variables. `cohomology` takes the actual cohomology of
that module-valued complex.

For a fixed smooth representation `V`, `homFunctor` is the module-valued
functor `Hom(V, -)` implemented by Mathlib's linear coyoneda. Its additivity
gives `fromRepresentation`, which applies it to every term of a genuine
complex `Q`. The proved `fromRepresentation_d_apply` states that the
differential sends `f : V ⟶ Q.X n` to `f ≫ Q.d n m`.
`precomposeRepresentation` constructs natural chain maps when `V` changes.
`fromRepresentationCohomology` takes the resulting cohomology modules.

The coefficient ring is commutative, the group has a topology, and no
topological group axiom is required merely to use the published smooth
category. The coefficient-ring, group and representation-carrier universes
are independent. The resulting morphism modules lie in the
representation-carrier universe. The representation modules have no topology.

## Source and exact scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), printed p.309, Proposition 4.4 and
equation (4.4.1), specifies that Ext is the derived functor of Hom in the
category of smooth coefficient representations. Printed pp.305-306,
equations (2.4)-(2.6), construct the projective-complex input used later.
Worker 13 read these passages. This module implements the underlying Hom
complex operations on actual smooth representations, with the source's
torsion coefficient rings included in the stated general coefficient scope.

This does not identify an arbitrary supplied complex with a projective or
injective resolution, and it does not name its cohomology derived Ext.
No abelian structure or enough-injectives result for the smooth category is
assumed here. Those constructions and the resolution comparison are separate
obligations, as are Harris's geometric input, particular double complexes,
spectral sequence and local-global comparison.

The construction is internal to the published representation category and
Mathlib's `CategoryTheory/Linear/Yoneda.lean` and homological algebra, at
commit `5ed2965256430c3649e86755f9576b54eca72435`. The companion
`LinearHomComplex.md` records the differential convention and intrinsic
proofs. The category import was checked in Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`.

Registered original: `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
