# Tuple independence of actual stable-image Jacquet lifts

Authors: Worker 119 and Worker 48 (suggested chamber-dominance route).

The closing theorem `Langlands.Jacquet.blockStableImageTupleIndependence` proves
exactly the published `BlockStableImageTupleIndependenceClause F T B V`.
The public theorem `stableImage_blockScalar_eq` exposes the actual equality
of submodules and works for every smooth representation. The closing theorem
uses the smoothness component of the published admissibility hypothesis.
The field and representation universes remain independent, and all primes,
p-adic fields, supplied topological data, ranks, and block shapes are retained.

## Implemented proof

The helper `weak_pow` proves closure of the weak chamber under natural powers
using its identity and multiplication laws. The helper `exists_weak_quotient`
fixes a strict tuple a and any unit tuple d. For each ordered block pair, the
normalized ratio of d is strictly positive because it is a unit of the
nonnegative reals. Apply the published `strictPowersEventuallyDeep` with this
positive ratio as depth. Two finite eventual conjunctions give one exponent r
whose a-power ratios are below the corresponding ratios of d for every forward
pair. The ratio homomorphism laws now show that a^r * d^(-1) is weakly
contracting. No minimum over a nonempty set of block pairs is needed.

Write C(a) for the existing normalized compressed action. Its identity and
the published `blockCompressedAction_mul` imply C(a^r) = C(a)^r for weak a.
To prove containment of the stable image for strict a in that for strict b,
fix an arbitrary natural exponent m. Apply the preceding helper with d = b^m,
and put c = a^r * (b^m)^(-1). Then c and b^m are weakly contracting, and
b^m * c = a^r. Multiplicativity therefore gives

    C(a)^r = C(b)^m * C(c).

If v belongs to every a-power range, write v = C(a)^r w. The displayed
identity gives v = C(b)^m (C(c) w), so v belongs to the m-th b-power range.
The existing `mem_stableImage` characterization turns this into containment
of the actual all-power intersections. Interchanging a and b proves equality
by antisymmetry. The order of composition puts the b-power on the left, as
required by this range witness.

The argument includes exponent zero, rank zero, empty and one-block shapes,
and the zero representation. Finite conjunctions over empty index types and
vacuous forward-ratio conditions require no exceptional hypotheses. It uses
only smoothness, compactness, block Iwahori factorization, and the stated
strict contractions. Finite-dimensional stabilization, identification of
Jacquet kernels, quotient surjectivity, and canonical-lift bijectivity are
not inputs. The closing target retains exactly its existing admissibility
hypothesis and does not weaken or modify the Library statement.

## Provenance

This is an internal chamber-cofinality derivation from the published
`CanonicalLiftDefinitions`, `BlockIwahoriDefinitions`, `BlockCompressionProof`,
and `BlockContractionProof`. Worker 48 supplied the suggested route in the
task context; Worker 119 implements it using finite eventual conjunctions.
The source motivation and Casselman canonical-complement discussion are
recorded in the unchanged `CanonicalLiftCompatibilityStatement.md`. The
present proof is not claimed to follow a numbered source argument and makes
no comparison with Casselman's unnormalized double-coset operator. It proves
only the tuple-independence clause; the separate nested-averaging clause and
aggregate compatibility statement remain outside this module's scope.
