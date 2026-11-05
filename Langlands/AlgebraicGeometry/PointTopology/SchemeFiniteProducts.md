# Finite products of actual scheme point spaces

Author: Worker 208.

This derived construction supplies finite-product topology infrastructure for
Conrad's *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Proposition 3.1, printed page 4, and Example 4.2, printed page 10.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Proposition 3.1 requires compatibility with fiber products for locally finite-type
schemes over a local topological ring with open units and continuous inversion.
Example 4.2 uses a finite product of Weil schemes after scalar base change.
This module derives the finite-product consequence from the published
`schemeProductPointHomeomorph` and Mathlib's construction of finite products from
binary products and a terminal object. The arbitrary-scheme, relative scope is
the generalization already supplied by that published binary comparison.
All point spaces retain their independently defined `schemePointTopology`.

The base `R` and value ring `S` are commutative rings in a common universe.
The ring `S` is a local topological ring with open units and continuous inversion,
as encoded by `IsOpenUnits`. No topology is imposed on `R`.
The index type is finite, possibly empty. All schemes are actual schemes over
`Spec R`; no affine, finite-type or separation hypotheses are used.

`schemePointTopCatFunctor` packages actual relative points and the existing
`schemePointContinuity_proof` into a functor to topological spaces. Its action on
a relative scheme morphism `f` is exactly `p ↦ p ≫ f`; the functor equations are
the identity and associativity laws of actual scheme morphisms.
`schemePointTopCatIsTerminal` uses uniqueness of morphisms into a terminal
scheme to construct its terminal topological point space: from any topological
space the constant map with value the unique relative point is continuous,
and every competing map agrees pointwise with it.
Binary-product preservation follows from `schemeProductPointHomeomorph`:
its exact projection formula identifies the mapped scheme product cone with
the ordinary product cone in topological spaces. A cone isomorphism transfers
the limiting property; an isomorphism of diagrams then handles every diagram
of binary-product shape. Mathlib's
`PreservesFiniteProducts.of_preserves_binary_and_terminal` then proves
finite-product preservation, after passing terminal preservation to the
empty-diagram shape.

For any actual limiting fan `c` on the finite family `X`,
`schemeFiniteProductPointHomeomorph` compares the actual points of `c.pt`
with the dependent product of actual points of `X i`. It is obtained by
uniqueness of product cones in topological spaces. Its apply theorem states
that component `i` is exactly postcomposition with `c.proj i`.
`schemePointTopCatFanIsLimit` records the intermediate limiting mapped fan;
`TopCat.piFanIsLimit` supplies the ordinary dependent product with its product
topology. The apply theorem is the projection identity of the canonical
isomorphism between these two limiting cones. No endpoint topology is defined
by transporting another topology. These are intrinsic construction laws.
This is a general-ring consequence of the existing local point-topology
theorems and is not a separate assertion stated verbatim in Conrad.

The source-specific Weil specialization, completed tensor algebras, all
upper-place factors, integral models and the global adelic comparison remain
separate obligations.
