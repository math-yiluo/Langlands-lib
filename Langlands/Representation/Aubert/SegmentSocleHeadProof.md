# Aubert exchange of the actual segment socle and special head

Author: Worker 165. The proof uses the published signed-Jacquet head
identification contributed by Worker 1186.

`Langlands.Aubert.segmentSocleHead` proves exactly the published
`Langlands.Aubert.SegmentSocleHeadStatement`. For every supplied actual strong
segment socle `πZ` and special head `πS`, the existing unadjusted alternating
induction–Jacquet operator sends `[πZ]` to
`(-1)^(Δ.degree-Δ.length) • [πS]`. The brackets are the canonical actual
finite-length classes, with finite length obtained from the irreducibility
clauses in the two strong constituent relations.

The prime, p-adic field and supplied topology are arbitrary. The field and
carrier universe parameters remain independent, and the actual smooth
representation carriers are saturated at `max uF uV`. The increasing segment
induction, upper block parabolic, positive half-modulus covariance, right
translation, strong image uniqueness and strong kernel uniqueness are the
unchanged constructions in the target. The Grothendieck group retains the
relations of all actual short exact sequences, including nonsplit ones.
No constituent existence is asserted.

The proof takes the actual embedding of `πZ` into the increasing segment
induction supplied by the strong socle relation. The supercuspidal tensor is
irreducible, hence finite length, and normalized induction preserves finite
length. The canonical factor-vector support criterion therefore identifies
`πZ` as an actual subquotient of this finite-length induction.
`segmentInductionAubertImage` produces an actual irreducible representation
whose class, up to sign, is its Aubert image. The two resulting sign cases
are supplied to `segmentSocleHead_of_signedIrreducibleImage`, which gives
the exact asserted sign and identifies that representation with `πS`.

The local irreducible-image input is proved in
`SegmentInductionAubertImage`, without an irreducible-image or effectivity
premise. Its support theorem comes from the actual geometric filtration:
each induction-after-Jacquet term acts by a natural scalar on the full
quasicuspidal induction class. Nonnegative actual factor multiplicities
force each supported column, and then their alternating sum, to stay in
that induction's support. Minimal nonzero Jacquet descent and nonassociated
quasicuspidal subquotient vanishing detect every constituent at the uniform
source shape. The associated segment Jacquet simple filtration has distinct
scalar eigenvalues, so the total Jacquet factor vector has multiplicities
at most one. Positive nonzero columns then make the uniform Jacquet map
reflect effectivity on this entire support.

Actual reversed Jacquet compatibility and hereditary quasicuspidality
compute the Jacquet image of the sign-adjusted Aubert vector as the factor
vector of an actual transported Jacquet object. Reflection gives
effectivity of that vector. Induction commutation and the quasicuspidal
eigenvalue make the same signed operator fix the full induction class;
the independent Aubert involutivity proof gives injectivity. Generic
positive integral counting for a fixed actual factor vector forces each
supported irreducible image to be one generator, and actual realization
gives the required irreducible representation. Thus the local-image
argument discharges all its positivity and fixed-class hypotheses.

The final reduction is the published
`SegmentSocleHeadReduction`. It applies actual reversed Jacquet exchange
to the supplied signed irreducible image. The published
`SegmentSignedJacquetHead` argument compares actual composition factors and
their scalar-separated subobjects, obtains a nonzero map to the decreasing
segment tensor, and uses normalized Frobenius reciprocity and the supplied
strong head to identify the output. Nonnegative actual multiplicities
force the relative sign to be positive, leaving precisely
`(-1)^(Δ.degree-Δ.length)` for the unadjusted operator.

This is an internal geometric and integral-lattice derivation of the segment
case recorded in the target statement, whose source is Aubert's Theorem 2.3
with the sign convention of Remark 2.2. It does not use the printed proof's
multisegment-classification route. The substantial lower inputs are actual
normalized exactness and finite-length preservation, the geometric lemma,
minimal Jacquet descent, quasicuspidal vanishing, scalar separation,
Frobenius reciprocity, induction/Jacquet compatibility, involutivity and
positive integral counting. No analytic classification, multisegment
exhaustion, ordered strong-head existence, quotient coverage, tempered-block
uniqueness, square-integrable classification or exhaustion, or regular
exhaustion is used.
