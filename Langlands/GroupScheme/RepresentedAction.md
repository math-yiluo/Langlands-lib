# Automorphic actions on represented invariant subgroups

This module derives an action on an actual represented invariant subgroup from
the published `AutomorphicAction` and `SubgroupFunctor.IsRepresentedBy` APIs.
The base is any scheme `S`. All assertions quantify over every test scheme over
`S`, including nonreduced tests. No affineness, smoothness or finiteness hypothesis
is imposed.

## Construction and internal provenance

All new declarations are in `Langlands.GroupScheme.AutomorphicAction`.
For `a : AutomorphicAction H G` and `F : SubgroupFunctor G`,
`IsStable a F` says that every action point in `H(T)` preserves `F(T)` for every
`T : Over S`.

Suppose an actual homomorphism `i : C ⟶ G` represents `F`, with witness
`hi : F.IsRepresentedBy i`, and `hF : a.IsStable F`. Representation means
that `i` is a monomorphism of schemes over `S` and its range is exactly `F`
on all tests. Apply stability to the universal points on `H.X ⊗ C.X`.
The resulting ambient action point belongs to the range of `i`, so it factors
through `C.X`. `representedActionHom` chooses this factorization, and
`representedActionHom_comp` proves its inclusion equation.
`lift_representedActionHom_comp` pulls this equation back along a product
pairing and uses naturality of the ambient action.

`onRepresentedSubgroup` packages that actual morphism as an automorphic action
of `H` on `C`. To prove its three intrinsic laws, compose with `i`, use the
inclusion equation and the homomorphism laws of `i`, apply the corresponding
ambient action law, and cancel the monomorphism.
`onRepresentedSubgroup_act_comp` states its equivariance on all tests:

`i(a_C(h,c)) = a(h,i(c))`.

`onRepresentedSubgroup_hom_unique` says that any other automorphic action
with the same universal inclusion equation has the same underlying action
morphism. It follows directly by monomorphism cancellation.

These are internal derived constructions. The only inputs are the published
action morphism and its laws, the published all-test subgroup representation,
universal points, composition, and monomorphism cancellation. No new external
mathematical assertion is used.

## Fixed subgroups for a commutative acting group

Let `A : CommGroupScheme S`, let `a` act on `G`, and let
`j : K ⟶ A.toGrp` be any group-scheme homomorphism.
`fixed_restrict_isStable` proves that `(a.restrict j).fixedSubgroup` is
stable under the whole group `A`. On every refinement, commutativity of `A`
permits the actions of `j(k)` and the restricted point of `A` to commute;
the fixed-point equation then gives the result. Neither `K` nor `j` is assumed
smooth, a torus or a subgroup inclusion.

For an actual representing homomorphism `i : C ⟶ G` with witness
`hi : (a.restrict j).fixedSubgroup.IsRepresentedBy i`,
`onRepresentedFixedSubgroup` constructs the resulting `A`-action on `C`.
`onRepresentedFixedSubgroup_act_comp` gives its equivariance with the inclusion.
`onRepresentedFixedSubgroup_restrict_act` proves that the restriction along
`j` acts trivially on `C(T)` for every test `T`. Its proof uses the represented
fixed-point condition on the image of a `C`-point, then cancels `i`.

Applied to a torus action restricted to a character kernel, this supplies the
action on a representing fixed centralizer and the triviality needed before
quotient-action descent. Representability remains an explicit premise;
this module neither constructs that centralizer nor descends an action to a
quotient. It does not assert relative root groups, smoothness, or a choice of a
primitive cocharacter.
