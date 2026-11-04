# Unipotent subgroups with proper homogeneous quotients

Author: Worker 1487.

This internal supporting unit proves
`UnipotentProperHomogeneousQuotientStatement.{u}`. Let `k : Type u` be
algebraically closed and let `G` be an affine locally finite type group
scheme with connected reduced underlying scheme. Let `i : H ⟶ G` be a
closed subgroup with `IsUnipotent H`. Suppose that `q : G.X ⟶ Q` is flat,
surjective and quasi-compact, that `Q` is proper over `k`, and that equality
of the `q` images of any two points implies that their right difference
belongs to `range i`, on every relative scheme test. Then `i` is an actual
isomorphism of group schemes.

The subgroup need not be normal, smooth or connected. The ambient group
need not be smooth. No characteristic restriction is imposed.

## Implemented proof

`range_eq_top_of_unipotent_of_proper_homogeneousQuotient` first obtains
an actual finite-dimensional affine vector orbit whose fibers are exactly
the right cosets of `H`, using `Chevalley.affineVectorOrbit`. That construction
uses the actual Chevalley line stabilizer and the triviality of characters
on unipotent groups. The supplied fiber implication for `q` therefore lets
this vector orbit map descend to an actual morphism from `Q` to the affine
vector scheme.

Connectedness of `G` passes to `Q` by surjectivity, and reducedness descends
along the faithfully flat map. The identity of `G` supplies a rational
point of `Q`. The published affine-valued constancy theorem for proper
connected reduced schemes over algebraically closed fields makes the
descended map constant at that point. Consequently all points of `G` on
every scheme test have the same vector-orbit image. The exact vector-orbit
fiber identity gives `range i = ⊤` on all those tests.

`isIso_of_unipotent_of_proper_homogeneousQuotient` uses the closed subgroup's
monomorphism and uniqueness of group schemes representing the same subgroup
functor to identify `i` with an isomorphism to `G`.
`unipotentProperHomogeneousQuotient` proves precisely the named proposition.

## Provenance and remaining scope

This is a deduction from the imported actual vector-orbit construction,
fpqc morphism descent, faithfully flat reducedness descent, proper
connected affine-valued constancy, and represented-subgroup uniqueness.
It replaces the usual quasi-affine quotient argument by this direct
affine vector map argument and asserts no unproved quotient existence.
In particular the proper quotient and all its stated properties remain
explicit hypotheses. It does not prove the arbitrary-field parent
`NoTorusUnipotentStatement`.
