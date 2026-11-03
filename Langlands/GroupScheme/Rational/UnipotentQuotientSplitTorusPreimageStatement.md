# The preimage of a split subtorus under a quotient by a unipotent subgroup

Author: Worker 1413.

`Langlands.GroupScheme.UnipotentQuotientSplitTorusPreimageStatement.{u}` is
an unproved proposition at arbitrary universe `u`. For every field
`k : Type u` and actual group scheme `G` over `Spec (CommRingCat.of k)` with
`Smooth G.X.hom`, `ConnectedSpace G.X.left` and `IsAffineHom G.X.hom`, it
takes

- an actual group scheme `U` and a homomorphism `r : U ⟶ G` with
  `IsClosedSubgroup r`, `Smooth U.X.hom`, `ConnectedSpace U.X.left` and
  `IsUnipotent U`;
- an actual group scheme `Q` and a homomorphism `q : G ⟶ Q` with
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q`;
- a commutative group scheme `B` and a homomorphism `z : B.toGrp ⟶ Q` with
  `IsSplitSubtorus z`.

It concludes that there are an actual group scheme `H` over the same base
and a homomorphism `j : H ⟶ G` such that

- `IsClosedSubgroup j`;
- `Smooth H.X.hom`, `ConnectedSpace H.X.left` and `IsAffineHom H.X.hom`;
- `IsSolvableGroupScheme H`;
- for every actual group scheme `K` over the same base and homomorphisms
  `i : K ⟶ G` and `g : K ⟶ B.toGrp` with `g ≫ z = i ≫ q`, there is a
  homomorphism `f : K ⟶ H` with `f ≫ j = i`.

The last clause is the only link between `H` and the data `q`, `z`: it says
that `H` contains every subgroup of `G` whose image under `q` lies in `B`,
expressed through actual homomorphisms on every relative scheme test. The
intended `H` is the preimage `q⁻¹(B) = G ×_Q B`, but the statement only
asserts existence. It does not claim that `H` is contained in `q⁻¹(B)`,
nor that `H` is the smallest such subgroup.

## Published interfaces

The module imports `Langlands.GroupScheme.Rational.SplitTorus`,
`Langlands.GroupScheme.Rational.RootSubgroupStructureStatement` and
`Langlands.GroupScheme.Absolute.Borel` unchanged.

- `IsClosedSubgroup j` says that the underlying scheme map of `j` is a closed
  immersion.
- `IsUnipotent U` says that every nonzero finite-dimensional matrix
  representation of `U` over `k` has a nonzero fixed vector.
- `RelativeRoot.IsFppfQuotient N q` says that the underlying scheme map of
  `q` is flat, surjective and locally of finite presentation and that the
  all-test image of its actual kernel is `N`.
- `IsSplitSubtorus z` says that `B.toGrp` is a split torus and `z` is a closed
  subgroup.
- `IsSolvableGroupScheme H` is the published solvability of the abstract
  group of geometric points of the base change of `H` to an algebraic
  closure of `k`.

No normality hypothesis on `r` is needed beyond what the quotient predicate
already provides, and no smoothness, affineness or connectedness of `Q` is
assumed. In the intended application `r` is a represented ground-field
unipotent radical, `q` is the published pseudo-reductive quotient and `z` is
the largest central split torus of `Q`.

## Source and derived provenance

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second
edition (2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`,
SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Printed page `p` is PDF page `p + 26`.

- Proof of Theorem C.2.3, printed p.593 (PDF p.619): with `U = R_{u,k}(G)`
  and `S` the maximal central `k`-split torus of `G/U`, "the preimage `H` of
  `S` in `G` is a smooth connected solvable `k`-subgroup of `G` that contains
  all `k`-split tori of `G`".
- Proof of Lemma 2.2.3, printed p.63 (PDF p.89): the preimage of a `GL_1` in
  `G/R_{u,k}(G)` "is a smooth connected affine `k`-group that is an extension
  of `GL_1` by `R_{u,k}(G)`".
- Proof of Proposition C.2.4, printed p.594 (PDF p.620): the preimage of a
  `k`-torus under the quotient by `R_{u,k}(P)` is a smooth connected solvable
  `k`-subgroup, an extension of the torus by the unipotent radical.

This statement is derived. It abstracts the preimage construction used in
these passages to an arbitrary smooth connected unipotent closed subgroup
`U` with a represented fppf quotient and an arbitrary split subtorus of the
quotient. The source's containment of subgroups in the preimage is expressed
as the factorization property for all homomorphisms whose composite with `q`
lands in `B`. No project errata file for this source was present when this
statement was prepared.

## Retained proof obligations

This file defines a proposition and supplies no proof. A proof must construct
the preimage as an actual closed subgroup of `G` (for instance the fibre
product `G ×_Q B` with its group structure), prove that it is smooth (it is
an fppf `U`-torsor over the smooth `B`), connected (a flat surjection with
connected fibres onto the connected `B`) and affine, and prove solvability of
its geometric points as an extension of the commutative group `B(k̄)` by the
unipotent group `U(k̄)`. Finally it must prove the factorization property from
the universal property of the fibre product.
