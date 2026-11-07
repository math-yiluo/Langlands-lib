# Uniqueness of normalized finite relative local invariants

Worker 1556 develops this derived helper for the actual local Weil class-map
proof. It uses the existing local invariant family and the proved unramified
`H²` exhaustion; it does not construct a Weil map or identify a Weil extension
class.

The main theorem `relative_eq_localInvariantFamily` says that inflation compatibility and arithmetic
normalization determine the relative invariant on every finite Galois extension
of a p-adic field, in an arbitrary common carrier universe. It does not claim
uniqueness of the absolute maps of an `InvariantFamily`, which these hypotheses
do not constrain.

On a finite unramified stage the positive carry class of a uniformizer generates
`H²`. Arithmetic normalization determines the map on that generator. For a
general finite Galois extension, embed it in the algebraic closure and represent
its absolute inflation by an unramified finite stage. Inflate both classes to the
compositum. Injectivity of closure inflation makes them equal there, so inflation
compatibility reduces their invariant values to the unramified comparison.
Inflation along the isomorphism onto the original extension's image gives the
result for its original carrier and algebra structure.

All ingredients are imported published Lean results. The proof is an internal
consequence of their exact statements, with no additional mathematical source
claim. The final equality compares only the relative homomorphisms.

The final corollary `relative_eq_of_normalized` compares any two such families
by comparing each with `localInvariantFamily unramifiedH2Exhaustion p`.
The proof is uniform in the common carrier universe `u`; it assumes no absolute
invariant identities or extra finite-relative image hypothesis.

The derived `relativeImages_of_normalized` transfers injectivity and the exact
denominator-subgroup image from the constructed invariant. Consequently
`normalizedRelativeInvariantEquiv` constructs an additive equivalence from
relative second cohomology to that subgroup under only the two normalization
laws. Forgetting subgroup membership recovers the supplied relative invariant.
