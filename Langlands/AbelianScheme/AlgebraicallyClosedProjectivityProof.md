# Projectivity over an algebraically closed field

`Langlands.GroupScheme.algebraicallyClosedProjectivity` proves exactly the
published proposition
`Langlands.GroupScheme.AlgebraicallyClosedProjectivityStatement.{u}`.
For every field `K : Type u` with `IsAlgClosed K` and every actual commutative
group object `G` over `Spec K`, smoothness, properness and geometric
connectedness imply `Langlands.AlgebraicGeometry.IsHProjective G.X.hom`.
The theorem has no additional hypotheses.

The conclusion uses the published polynomial-Proj construction unchanged:
there exist `n : ℕ` and a scheme morphism
`i : G.X.left ⟶ ProjectiveSpace K n` such that `i` is a closed immersion and
`i ≫ projectiveSpaceToSpec K n = G.X.hom`.

## Implemented proof

Fix the field, group object and three geometric hypotheses of the target.
The published theorem
`Langlands.GroupScheme.algebraicallyClosedSeparatingLineBundle`, imported from
`Langlands.AbelianScheme.AlgebraicallyClosedSeparatingLineBundleProof`, gives
an actual line bundle `L` on `G.X.left` with
`Picard.SeparatesPointsAndTangents G.X.hom L`. Its complete linear system is
base-point free on rational points and separates distinct rational points
and nonzero dual-number tangent vectors.

Apply the published theorem
`Langlands.AlgebraicGeometry.separatingLineBundleHProjectivity`, imported from
`Langlands.AlgebraicGeometry.SeparatingLineBundleHProjectivityProof`, to
`K`, `G.X.left`, `G.X.hom`, `L`, the given properness proof and this separation
property. It returns precisely `IsHProjective G.X.hom`.

The first input obtains its separating bundle from a finite section seed
and the theorem of the square, using tensor cubes and triple translates.
The second input extracts finitely many separating sections, constructs
their morphism to the actual polynomial-Proj projective space, and proves
that this proper morphism is a closed immersion. Their companions describe
those proofs. Both inputs are unconditional published theorems; no seed,
square, separation or projectivity certificate is a premise of this theorem.

## Provenance and scope

This is a derived composition implementing the final step of the
algebraically closed part of Milne's Theorem 7.1, *Abelian Varieties*,
author revision January 2, 2022, pp.10–11, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The source correspondence and errata are recorded in the companions of
the target and the two imported proofs. Hartshorne's criterion is used
through the published very-ampleness proof; this module does not rely
directly on Hartshorne's book.

The universe `u` is arbitrary. The proof retains every characteristic and
dimension zero, with no positive-dimension condition; the permitted
projective-space dimension `n` is any natural number. It does not add
geometric-integrality, finite-type or separatedness premises. It uses no
abelian ample-existence theorem or downstream consequence, and it performs
no descent to a field that is not algebraically closed.

Worker 2088 wrote this composition and its explanation. Authorship of the
imported constructions and proofs is recorded in their companions.
