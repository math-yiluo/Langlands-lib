# Natural inner corrections of comparisons of pinned models

`RelativePinnedComparisonExistenceStatement.{u}` is a proposition, not a theorem.
It asserts the existence of the `RelativePinnedComparison` structure defined in
this module. No existence proof, new axiom, or automorphism scheme is supplied.

## Data and exact conclusion

The operation takes two supplied `AffinePinnedModel`s `M` and `N`, an arbitrary
scheme `T`, maps `f : T → M.base` and `g : T → N.base`, and an actual isomorphism
`e : M.groupOver f ≅ N.groupOver g`. It returns another actual isomorphism
`compare M N f g e` with the same endpoints. The models can have different
original rings, coordinate index types, and root index types. Their full
coordinate root data, bases and pinning vectors are part of the supplied models.

The required properties are:

1. Identity comparisons are preserved.
2. Compositions of comparisons are preserved, even for three different models.
3. For every scheme morphism `q : W → T`, comparison commutes with
   `AffinePinnedModel.pullComparison`, including its actual direct/iterated
   base-change identifications.
4. The output carries the chosen coordinate torus to the chosen coordinate
   torus. An actual torus isomorphism `τ` gives the exact inclusion square.
5. The output carries the actual cocharacter of the sum of positive coroots for
   the source base to the corresponding target cocharacter. These are the
   published `BasedBorelTransport.cocharacter`s on the normalized pullbacks.
6. Let `p : M.groupOver f → A` be any supplied fppf quotient by the full centre,
   and let `c` be any supplied action of `A` whose restriction along `p` is
   conjugation. There is a section `x ∈ A(T)` whose actual automorphism is
   `e ≪≫ (compare M N f g e).symm`.

In the last formula the composite first applies the original comparison and
then the inverse of the corrected comparison. It is an automorphism of the
source group. A section is the actual morphism
`Over.mk (𝟙 T) ⟶ A.X`; `c.basePointIso x` is its actual action on that group.
The centre and quotient are the unchanged all-test Library definitions. This is
a global adjoint section on `T`, not a conjugating section of the source group
required to exist on `T`. No quotient or action is constructed by the statement.

All refinements and common schemes are arbitrary: there are no connectedness,
local connectedness, affineness, quasi-compactness, or nonemptiness hypotheses on
`T` or `W`. The output is an actual isomorphism. The statement does not require
one constant root-datum equivalence to describe it on all of `T`; its outer class
may vary locally. The structure specifies the properties above rather than a
unique operation or a formula for the pinning vectors of the output.

## Source and derivation

This is a derived consequence of Brian Conrad, *Reductive group schemes*
(2014), registered as `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Printed and one-based PDF page numbers agree.

- Theorem 6.1.17, p.197, identifies pinned split reductive groups and based root
  data, with isomorphisms as morphisms. It provides the unique pinned lift of a
  specified based root-datum equivalence, compatible with the splittings.
- Theorem 7.1.9(1), p.245, gives the automorphism-group exact sequence with inner
  subgroup `G/Z_G`. Part (3), p.246, identifies the outer sheaf for a pinned split
  group with the constant group scheme of based root-datum automorphisms, and
  gives the semidirect product splitting defined by the pinning.
- The proof on p.246 explicitly treats points over arbitrary `S`-schemes `S′`
  and proves equality of the group sheaves by working Zariski-locally on `S′`.
  Thus its conclusion is not limited to connected base points. Sections of a
  constant group scheme are allowed to be locally varying.

To derive the stated comparison operation, work locally on the common scheme
with the pinned groups obtained by pulling back the two affine models. The
original isomorphism determines an outer comparison of their based data. The
unique pinned lift supplies the corrected comparison. For different models this
is the isomorphism-torsor version of the automorphism splitting: after a local
pinned identification of the two models, apply Theorem 7.1.9(3), and then remove
that identification. Uniqueness of pinned lifts makes the result independent of
this auxiliary identification. It also makes the local results agree on
intersections, makes them commute with arbitrary pullback, and makes them
preserve composition. The resulting morphisms glue as actual morphisms between
the supplied group schemes. No descent of a new group scheme is used here.

Pinned lifts preserve the torus and act by based root-datum equivalences. Such
equivalences preserve the sum of positive coroots, which gives the exact
cocharacter equality, using the published exponent transport identities. The
ratio of an isomorphism and its pinned correction lies in the inner subgroup.
The semidirect product description gives a section of `G/Z_G` on the whole
common scheme. Every supplied full-centre fppf quotient and action as in clause
6 realizes this same subgroup and its conjugation action, so the section gives
the stated equation. Conrad's theorems state nonempty bases; on an empty common
scheme the isomorphisms and sections are unique and all clauses are automatic.

## Scope

This proposition isolates the sheaf-level pinning input needed to correct
transitions on arbitrary overlaps. It does not assert representability of the
automorphism functor, choose a single global split form, construct an étale
splitting cover, descend an object, or prove existence of a quasi-split inner
form. The connected-affine base-point statement
`AffinePinnedAutomorphismGroupStatement` is related but does not provide the
naturality or locally varying comparisons asserted here. A separate proof is
required for this proposition.
