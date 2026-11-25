# Idempotent centralizer loci for diagonalizable subgroups

This internal development derives open centralizer loci from the published
character embedding, conjugation, grouplike coefficient and affine cutout
constructions. Its algebraic input is the finite-character idempotent identity
locus in `GrouplikeIdentityLocus`.

For an algebra point normalizing an embedded diagonalizable group, its
conjugated universal character becomes the identity after an algebra map if and
only if the refined point centralizes the embedded characters after every
further algebra map. Thus one idempotent detects all-test centralization when
the character group is finitely generated, including torsion character groups.

The geometric result uses a corepresented group functor over a commutative ring
and a monomorphism from the diagonalizable group of a finitely generated
abelian character group. The subgroup must have an ideal cutout on all tests,
and the quotient of the ambient coordinate algebra by that ideal must be
projective over the base. These hypotheses allow the published ideal-cutout
results for both the normalizer and the centralizer to apply.

For any normalizing family over any parameter scheme, `exists_openLocus`
constructs a basic open in that scheme. A test morphism has range in this open
precisely when its induced family lies in the full centralizer subgroup
functor. `openLocus` chooses such an open, and `range_subset_openLocus_iff`
records this all-test property. The parameter scheme need not be affine.

The proof first identifies membership in an affine ideal-cutout subgroup with
membership of the corresponding point on global sections. Apply the algebraic
idempotent lemma to the normalizing point on global sections. The resulting
idempotent defines a basic open. A morphism has range in this open exactly when
its pullback is a unit; an idempotent unit is one. Naturality of the point
comparison then gives the stated equivalence.

This module supplies open loci under the stated coordinate hypotheses. The
passage to arbitrary closed multiplicative-type subgroups by descent and the
quotient-existence theorem remain separate proof obligations.
