# Jacquet detection on segment induction support

Author: Worker 165.

This internal derivation concerns actual finite-length smooth representations
and their exact Grothendieck classes. It does not assert effectivity of the
Aubert operator.

`SegmentJacquetDetectionStatement` says that the full uniform Jacquet map,
transported to genuine irreducible factor vectors, reflects coefficientwise
effectivity on every signed vector supported in the increasing segment
induction's composition factors. The field, supplied topology, independent
field and carrier universes, and saturated carriers are arbitrary.

`jacquetOnIrreducibles` composes realization, the actual normalized Jacquet
class map, and composition-factor counting. Its actual generator formula and
positivity follow from the published normalized Jacquet exact-class formula
and finite-length preservation.

`uniformInductionJacquet_nontrivial` starts from an actual nonzero
subquotient of induction from uniform quasicuspidal data. Minimal nonzero
Jacquet descent supplies a nonzero quasicuspidal Jacquet object for some
shape. Nonassociated Jacquet vanishing on quasicuspidal subquotients forces
that shape to be associated to the source. Every shape associated to a
uniform shape is the same ordered shape, by the block-size and block-count
invariants of a conjugating permutation. Thus the full uniform Jacquet
object is nonzero. Actual Jacquet subquotient transport and hereditary
quasicuspidality also give the included quasicuspidality lemma.

A nontrivial actual finite-length object has a nonzero composition-factor
vector: its composition series has positive length and a chosen graded
factor has positive multiplicity. A simple series with distinct scalar
actions has every multiplicity at most one, since equivalent nonzero
graded factors have equal scalar actions.

For segment induction, the published associated Jacquet filtration is such
a separated simple series. Admissible Schur supplies the supercuspidal
base's scalar character, and the existing segment separating scalar has
distinct eigenvalues indexed by the factor permutations. Consequently the
total Jacquet factor vector has coefficients at most one. Each supported
irreducible is an actual subquotient, so the nonzero detection result and
positivity give nonzero positive columns of the Jacquet map. The generic
positive-lattice reflection theorem recovers each coefficient of any
supported signed vector from a coordinate of its Jacquet image.

The substantial inputs are actual exactness and finite-length preservation,
minimal Jacquet descent, nonassociated quasicuspidal subquotient vanishing,
associated Jacquet filtration and scalar separation, and elementary
integral-lattice reflection. These retain all actual short exact sequence
relations, including nonsplit sequences. No full segment Jacquet formula,
classification, exhaustion, signed effectivity or irreducible Aubert-image
theorem is assumed.
