# Affine split isomorphism assembly

This internal module reduces the unchanged affine split Isomorphism Theorem to
four explicit inputs. It works over every commutative ring in the same universe
as the target, with no local-ring, reducedness or nontriviality hypothesis.
The reduction is conditional; this module alone does not supply an unconditional
proof of the target.

## Common coordinate torus

`LocalSplitCell.exists_iso_comp_torus_of_weylRelations` takes two reductive groups
over `Spec R`, closed fibrewise maximal coordinate tori with a common coordinate
root datum, a base, descending simple words, and Weyl-normalized simple-root
and opposite-root parametrizations. It also takes the published local
commutator and negative-simple relation statements as hypotheses. The conclusion
is an isomorphism `ψ` with `i ≫ ψ.hom = i'`.

The proof enumerates the negative roots arbitrarily and the positive roots by
increasing height. The relation transport lemmas in `AffineSplitWeylRelations`
supply the hypotheses of the published arbitrary-ring
`localSplitCommutatorLawIsomorphism`. That assembly gives an isomorphism matching
the two cell maps. Restricting its cell-map equality to zero root coordinates,
using `torus_comp_of_cellMap_comp`, proves the torus compatibility.

## Full target reduction

`AffineSplitWeylRelationsReductionStatement.{u}` is the explicit proposition
that the following four inputs imply exactly
`AffineSplitIsomorphismTheoremStatement.{u}`.
`affineSplitIsomorphismTheorem_of_weylRelations` proves this reduction statement.
Its four premises are:

1. `h1`: over every commutative ring, a reductive group with a closed fibrewise
   maximal coordinate torus, its fibrewise root datum and free rank-one root
   spaces admits Weyl-normalized simple-root and opposite-root parametrizations
   for every chosen base.
2. `h2 : LocalSplitWeylCommutatorStatement.{u}`.
3. `h3 : LocalSplitWeylNegSimpleStatement.{u}`.
4. `htransport`: freeness of the root spaces for `Q` transports along the torus
   isomorphism attached to an equivalence `e : P ≃ Q` to freeness of the root
   spaces for `P` at `precompTorus e.weightEquiv i'`. Its precise scope is all
   commutative rings, all finite coordinate types and affine ambient groups;
   it assumes neither reductivity nor a fibrewise-root-datum realization.

Given the target's `f : Q ≃ P`, the proof precomposes the second torus embedding
with the integral-coordinate torus isomorphism associated to
`f.symm.weightEquiv`. Published common-torus transport preserves closedness,
fibrewise maximality and the root datum, and `htransport` supplies root-space
freeness. A base of the finite reduced root datum exists by the published
root-datum base theorem. Apply `h1` to both groups and use the descending words
and the preceding common-torus assembly to obtain `φ`.

The chosen torus isomorphism is
`LocalSplitCell.exponentEquivGroupIso _ f.symm.weightEquiv`. The common-torus
assembly already gives `i ≫ φ.hom = τ.hom ≫ i'` with this `τ`. Finally,
`splitTorus.pointsEquiv_exponentEquivGroupIso` evaluates its character pullback
on every test scheme. The inverse of `f.symm.weightEquiv` acts as `f.weightMap`,
which gives exactly the monomial identity required by the target.

## Provenance and remaining inputs

These are internal derived consequences of the imported published coordinate
cell and integral-coordinate torus constructions, the explicit relation
transport lemmas and the stated four premises. The module changes no target or
imported statement. The target's exact unconditional proof still requires
supplying those premises by independently accepted, published results.
