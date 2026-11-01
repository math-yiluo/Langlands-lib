# Etale restriction and actual associated coefficient sheaves

Author: Worker 13.

## Scope and conventions

Let `X` and `Z` be schemes in universe `u`, `f : Z ⟶ X` an etale morphism,
and `R : Type u` a commutative ring. Let `G : Type u` be an arbitrary group
and `Y : Action X.Etale G` an actual small-etale object with a deck action.
All sheaves take values in `ModuleCat.{u} R`.

Write `L` for the actual sheaf restriction
`EtalePullback.restriction f (ModuleCat.{u} R)` and `f*Y` for
`(etaleTorsorPullbackFunctor f G).obj Y`. Its underlying cover is the scheme
fiber product and its action is the base change of the original deck action.
The etale hypothesis on `f` supplies the composition functor from the small
etale site of `Z` to that of `X`. There is no finiteness, surjectivity or
torsor hypothesis on `Y` or `G`: the associated invariant sheaf can be formed
without these hypotheses.

The main construction is the natural isomorphism

`associatedFunctor X.smallEtaleTopology Y ⋙ L`
`≅ L.mapAction G ⋙ associatedFunctor Z.smallEtaleTopology (f*Y)`.

It applies to every action of `G` on an actual module sheaf on `X`,
including nonconstant coefficients, and to all equivariant coefficient
morphisms. Restriction and geometric base change are already constructed
functors; the displayed isomorphism is constructed here rather than supplied
as input.

## Product sections and deck maps

`etaleProductSheafPullback` compares `productSheaf V ⋙ L` and
`L ⋙ productSheaf (f*V)` for an arbitrary `V : X.Etale`.
At a sheaf `F` and a test object `U : Z.Etale`, its component applies
`F.obj.mapIso` to the opposite of the geometric product isomorphism

`siteMap f (f*V ×_Z U) ≅ V ×_X siteMap f U`

from `EtaleProductPullback`. Thus its direction is from sections of `F` on
the right-hand product to sections on the left-hand product.
The component is an actual sheaf isomorphism, with inverse supplied by the
inverse geometric isomorphism. Naturality in test objects follows from the
geometric comparison's naturality in the second factor; naturality in `F`
follows from the underlying presheaf naturality of each coefficient morphism.

`etaleProductSheafPullback_deck` proves that the comparison intertwines
restriction of `deckMap a F` with `deckMap (f*.map a) (L.obj F)`
for every endomorphism `a : V ⟶ V`. The proof applies the geometric
comparison's naturality in its first factor and contravariant functoriality
of the sheaf.

## Diagonal actions and invariant diagrams

`etaleDiagonalPullback` lifts the product-sheaf comparison to an isomorphism
of functors on coefficient actions. The diagonal action is the original
construction: inverse deck pullback by `Y.ρ g⁻¹`, followed by the coefficient
action `F.ρ g`. For each `g`, deck compatibility transports the first map,
and coefficient naturality transports the second map. These two equations
prove equivariance of the component isomorphism. Naturality in arbitrary
equivariant coefficient morphisms is the product comparison's naturality.

`etaleInvariantDiagramPullback` expresses the same comparison as a natural
isomorphism of the entire `SingleObj G`-indexed diagrams used to take
invariants. Each component at the unique index object is the product-sheaf
isomorphism; naturality along every group element is the proved diagonal
equivariance equation.

## Associated invariant limits

The local limit instance uses the actual limits of `ModuleCat.{u} R` for
the `SingleObj G` shape and hence the corresponding sheaf limits.
Restriction preserves these limits because it is the right adjoint in the
constructed `EtalePullback.extensionAdjunction f R`; this argument is
instantiated at the stated group universe.

`etaleAssociatedPullback` first applies `preservesLimitNatIso` to identify
restriction of the original invariant limit with the limit of the
restricted invariant diagram. It then applies the limit functor to
`etaleInvariantDiagramPullback`. Both steps are natural isomorphisms,
so the result is natural in the full coefficient action category.

`etaleAssociatedPullback_hom_inclusion` proves that the forward comparison,
followed by the invariant inclusion on `Z`, is restriction of the original
invariant inclusion followed by the product-sheaf comparison. The proof
uses the equation for the limit functor on projection maps and the
projection equation for the limit-preservation isomorphism.
`etaleAssociatedPullback_inv_inclusion` gives the inverse equation:
the inverse comparison followed by restriction of the original inclusion
is the new inclusion followed by the inverse product-sheaf comparison.
It follows by cancellation with the product-sheaf isomorphism and its
inverse identities.

## Provenance and remaining obligations

This is an internal derived comparison, using the existing actual
`Associated`, `EtaleTorsorPullback`, `EtaleProductPullback` and
`EtalePullbackAdjunction` constructions and Mathlib's categorical limits.
The proof route is the geometric product universal property, contravariant
sheaf functoriality, diagonal equivariance, and preservation of invariant
limits by a right adjoint. No additional literature theorem is asserted.

This module does not identify restriction of a constant sheaf with the
constant sheaf on the new base, nor compare the resulting constant-associated
functors. It does not supply cover-transition, group-restriction or
iterated-base-change coherence equations for this comparison. It does not
construct inverse image along non-etale base morphisms or realize Harris's
Shimura spaces and level torsors. Supports, traces, uniformization and
cohomological comparisons remain separate obligations.
