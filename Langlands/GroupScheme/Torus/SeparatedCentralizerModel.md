# Closed centralizers of relative tori in separated groups

Author: Worker 606.

`Langlands.GroupScheme.separatedRelativeTorusCentralizerModel.{u}` constructs
an actual closed representative of the whole centralizer of any relative-torus
homomorphism into a separated group scheme. The base scheme and universe are
arbitrary. The torus is a commutative group scheme `T/S` with
`RelativeTorus.IsTorus T.toGrp`, the ambient group has
`IsSeparated G.X.hom`, and the input map is an actual homomorphism
`t : T.toGrp ⟶ G`. The homomorphism need not be a closed immersion. No
smoothness, affineness, finite-type, quasi-compactness, connectedness or
reductivity assumption is imposed on the ambient group.

The result has the existing type
`SubgroupFunctor.ClosedRepresentative (torusCentralizer t)`. Its fields are
an actual group scheme `C`, a homomorphism `c : C ⟶ G`, closedness of `c`,
and the all-test representing condition. Thus `c` is a monomorphism and its
literal range is exactly the whole centralizer on every scheme over the base,
including nonaffine and nonreduced tests. Fixedness is tested after every
refinement of each test scheme. Smoothness and finite presentation of the
representative are not asserted.

## Implemented construction

For a diagonalizable group `D(Λ)` over `Spec R`, the helper
`Diagonalizable.free_coordinateModule` identifies its relative global sections
with the group algebra `R[Λ]` using `Corepresented.affineSectionsAlgEquiv`.
The group algebra is a free `R`-module, so the coordinate module is free as
well. The identity extension `R/R` is faithfully flat and makes the required
coordinate tensor product projective. This is the helper
`Diagonalizable.hasFpqcProjectiveCoordinateModule`. The structure morphism
of `D(Λ)` is affine, and is flat because the group algebra is free. These
steps require no finite-generation condition on `Λ`.

The published `fixedSubgroupRepresentability` applies to the conjugation
action of `D(Λ)` on any separated `G/Spec R`: its acting-group hypotheses
are exactly affineness, flatness and fpqc projectivity of the coordinate
module. Its ambient hypothesis is separation. The published equality between
the conjugation fixed subgroup and `torusCentralizer` gives an actual closed
centralizer. A split torus is isomorphic to the diagonalizable group of its
finite free exponent lattice. Precomposition with this actual isomorphism
preserves its range and hence its centralizer, giving the affine-base
split-torus result.

The helper `torusCentralizer_isClosedRepresentable_of_etaleCover` descends
closed representability along an arbitrary etale cover. It uses the published
all-test equality `torusCentralizer_eq_coverDescent`, the matching property
for base changes of a subgroup, and closed-subgroup descent. No hypothesis
on the ambient group is needed in this descent step.

For a split torus over an arbitrary base, apply the affine-base construction
on the affine open cover, viewed as an etale cover. Separation of `G/S` is
preserved under those base changes. Descend to obtain the closed representative
over the original base. For a general relative torus, use its supplied etale
splitting cover, apply this arbitrary-base split-torus result on each member,
and descend once more. The final constructor chooses the resulting actual
representative through
`SubgroupFunctor.ClosedRepresentative.ofIsClosedRepresentable`.

## Internal provenance

This is an internal application of the published fixed-subgroup representability
theorem, actual diagonalizable group schemes and their affine coordinate
comparison, all-test centralizer base change, and closed subgroup descent. It
introduces no new external mathematical theorem. The fixed-subgroup theorem
is imported by its Lean name from
`Langlands.GroupScheme.FixedSubgroupRepresentabilityProof`; its source
provenance is recorded with that published theorem. The present result supplies
the closed-representability part of the centralizer input for
`ReductiveFiberAffinenessStatement`. Further arguments are needed for any
smoothness claim or ambient affineness conclusion.
